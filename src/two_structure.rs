use std::collections::HashSet;
use std::collections::HashMap;
use regex::Regex;

use std::convert::*;
use rand::Rng;
// use std::str;
// use std::any::type_name;
// use std::any::TypeId;
// use crate::type_of;

#[derive(Debug)]
#[derive(Clone)]
pub struct TwoStructure {
    /// the graph of a two structure
    pub nodes: HashSet<u64>,
    /// list of sets, colors[i] contains the set of edges of color i
    pub colors: Vec<HashSet<(u64, u64)>>,
    /// only for quotient graph, contains the nodes of the graph if they are modules
    pub modules: Vec<HashSet<u64>>,
}

//impl Clone for TwoStructure {
//    fn clone(&self) -> Self {
//        *self
//    }
//}


impl TwoStructure {
    pub fn new() -> TwoStructure {
        let mut ts = TwoStructure {
            nodes : HashSet::new(),
            colors : Vec::new(),
            modules : Vec::new(),
        };
        let /*mut*/ s: HashSet<(u64, u64)> = HashSet::new();
        ts.colors.push(s);
        ts
    }


    /// Returns the module of a two-structure corresponding to the node 'node' of its quotient graph
    pub fn node_to_module(&self, node: u64) -> Option<&HashSet<u64>> {
        self.modules.get(node as usize)
    }

    pub fn slice(&mut self, nodes: HashSet<u64>) -> TwoStructure {
        let mut sts = TwoStructure::new();
        sts.nodes = nodes;
        let mut is_first = true;
        for c in &self.colors {
            if is_first {
                is_first = false;
            } else {
                let mut c_edges: HashSet<(u64, u64)> = HashSet::new();
                for edge in c {
                    if self.nodes.contains(&(edge.0)) && self.nodes.contains(&(edge.1)) {
                        c_edges.insert(*edge);
                    }
                }
                sts.colors.push(c_edges);
            }
        }
        sts
    }

    pub fn edge(&mut self, src: u64, dst: u64, col: u64) {
        if col == 0 {
            panic!("Color 0 is reserved (no edge marker)");
        }

        let e = (src, dst);
        for color in 1..self.colors.len() {
            if color as u64 != col {
                let ref_s: &HashSet<(u64, u64)>  = self.colors.get(color).unwrap();
                if ref_s.get(&e) != None {
                    panic!( "{}",
                            format!("Edge already existing with distinct color: {} -> {} (color {}))",
                                    src,
                                    dst,
                                    col
                            )
                    );
                }
            }
        }

        let l = self.colors.len() as u64;
        if col >= l {
            self.colors.resize((col + 1) as usize, HashSet::new());
        }
        self.colors.get_mut(col as usize).unwrap().insert(e);
        self.nodes.insert(src);
        self.nodes.insert(dst);
    }

    pub fn uedge(&mut self, src: u64, dst: u64, col: u64) {
        self.edge(src, dst, col);
        self.edge(dst, src, col);
    }

    /// return 0-color edges
    pub fn edges_zero(&mut self) -> HashSet<(u64, u64)> {
        let mut all_edges: HashSet<(u64, u64)> = HashSet::new();
        for u in &self.nodes {
            for v in &self.nodes {
                if *u != *v {
                    all_edges.insert((*u, *v));
                }
            }
        }
        for edge_set in &self.colors {
            for edge in edge_set {
                all_edges.remove(edge);
            }
        }

        all_edges
    }

    /// # return
    /// triplet of source, destination and color for all edges
    pub fn all_edges(&mut self) -> Vec<(u64, u64, u64)> {
        let mut v: Vec<(u64, u64, u64)> = Vec::new();
        for &edge in self.edges_zero().iter() {
            v.push((edge.0, edge.1, 0));
        }
        for color in 0..self.colors.len() {
            // for edges in self.colors.get(color) {
            if let Some(edges) = self.colors.get(color) {
                for &edge in edges {
                    v.push((edge.0, edge.1, color as u64));
                }
            }
        }
        v
    }

    pub fn all_edges_but_zero(&self) -> Vec<(u64, u64, u64)> {
        let mut result = Vec::new();
        for color in 1..self.colors.len() as u64 {
            for edge in &self.colors[color as usize] {
                result.push((edge.0, edge.1, color));
            }
        }
        result
    }

    pub fn color_of(&mut self, v1: u64, v2: u64) -> u64 {
        for color in 1..self.colors.len() {
            // for edges in self.colors.get(color) {
            if let Some(edges) = self.colors.get(color) {
                for &edge in edges {
                    if edge.0 == v1 && edge.1 == v2 {
                        // usize::try_into(color).unwrap_or(0)
                        return color as u64;
                    }
                }

            }
        }
        0
    }

    pub fn to_dict(mut self, color: u64) -> HashMap<u64, HashSet<u64>> {
        let mut dico = HashMap::new();
        for &node in &self.nodes {
            dico.insert(node, HashSet::new());
        }

        for (src, dst, col) in self.all_edges() {
            if col == color {
                dico.get_mut(&src).unwrap().insert(dst);
            }
        }

        dico
    }

    pub fn to_dot(&mut self, show_zero: bool, simple: bool) -> String {
        let mut dot = String::from("digraph {\n\n");
        dot.push_str("\t// nodes\n\n");

        let mut node_names: HashMap<u64, String> = HashMap::new();
        let mut node_index = 1;
        for node in &self.nodes {
            let node_name: &String = &format!("N{}", node_index);
            node_names.insert(*node, String::from(node_name));
            let mut fend = String::new();
            if simple {
                fend = String::from(node_name);
                fend.push_str(&*format!("N{}", node_index));
            } else {
                match self.node_to_module(*node) {
                    Some(v) => fend.push_str(&*node_to_str2(v)),
                    None => fend.push_str(&*format!("N{}", node_index)),
                };
            }
            dot.push_str(&format!("{} [label=\"{}\"];\n", node_name, fend).into_boxed_str());
            node_index += 1;
        }

        dot.push_str("\n\t// edges\n\n");

        for (src, dst, col) in self.all_edges() {
            if col != 0 {
                let mut ni = String::new();
                if !simple {
                    ni = String::from(format!("{}", col));
                }
                dot.push_str(
                    &*format!("{} -> {} [label=\"{}\"];\n",
                              node_names[&src],
                              node_names[&dst],
                              ni
                    )
                );
            } else if show_zero {
                dot.push_str(
                    &*format!("  {} -> {} [style=dotted];\n",
                              node_names[&src],
                              node_names[&dst]
                    )
                );
            }
        }

        dot.push_str("}\n");
        dot
    }

    pub fn from_dot(dot_content: &str) -> TwoStructure {
        let mut ts = TwoStructure::new();

        let node_re = Regex::new(r#"N(\d+) \[label="(\d+)"\];"#).unwrap();
        let edge_re = Regex::new(r#"N(\d+) -> N(\d+) \[label="(\d+)"\];"#).unwrap();
        let zero_edge_re = Regex::new(r"N(\d+) -> N(\d+) \[style=dotted\];").unwrap();

        for cap in node_re.captures_iter(dot_content) {
            let node = cap[1].parse::<u64>().unwrap();
            ts.nodes.insert(node);
        }

        for cap in edge_re.captures_iter(dot_content) {
            let src = cap[1].parse::<u64>().unwrap();
            let dst = cap[2].parse::<u64>().unwrap();
            let col = cap[3].parse::<u64>().unwrap();
            ts.edge(src, dst, col);
        }

        for cap in zero_edge_re.captures_iter(dot_content) {
            let src = cap[1].parse::<u64>().unwrap();
            let dst = cap[2].parse::<u64>().unwrap();
            // 0 color for no edge marker
            ts.edge(src, dst, 0);
        }

        ts
    }
}




pub fn node_to_str(node: u64) -> String {
    format!("{}", node.to_string())
}

pub fn node_to_str2(node: &HashSet<u64>) -> String {
    let mut buffer = String::new();
    buffer.push_str("{ ");
    for &elem in node {
        buffer.push_str(&*format!("{}", elem));
    }
    buffer.push_str(" }");
    buffer
}

// build two_structure //

/// Build a two structure from the provided 'dico'
/// which must represent an adjascency dictionary.
/// Each key is a node 'src', and if a node 'dst' is
/// an element of 'dico[src]', the there will be an
/// edge from 'src' to 'dst' in the resulting two structure.
/// The 'color' used is 1 by default, and all edges will have
/// the same global color.
pub fn twostructure_from_dict(dico: HashMap<u64, Vec<u64>>, color: u64) -> TwoStructure {
    let mut graph = TwoStructure::new();
    for key in dico.keys() {
        graph.nodes.insert(*key);
    }
    for (src, dests) in dico.iter() {
        for dst in dests {
            graph.edge(*src, *dst, color);
        }
    }
    graph
}

// diagraph examples //

/// An example of an undirected graph as a 2-structure.
/// from: A survey of the algorithmic aspects of modular decomposition.
///      Michel Habib, Christophe Paul.
///      Computer Science Review 4 (2010).
pub fn graph_ex1() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.uedge(1, 2, 1);
    g.uedge(1, 4, 1);
    g.uedge(1, 3, 1);
    g.uedge(2, 4, 1);
    g.uedge(2, 5, 1);
    g.uedge(2, 6, 1);
    g.uedge(2, 7, 1);
    g.uedge(4, 5, 1);
    g.uedge(4, 6, 1);
    g.uedge(4, 7, 1);
    g.uedge(3, 4, 1);
    g.uedge(3, 5, 1);
    g.uedge(3, 6, 1);
    g.uedge(3, 7, 1);
    g.uedge(5, 6, 1);
    g.uedge(5, 7, 1);
    g.uedge(6, 8, 1);
    g.uedge(6, 9, 1);
    g.uedge(6, 11, 1);
    g.uedge(6, 10, 1);
    g.uedge(7, 8, 1);
    g.uedge(7, 9, 1);
    g.uedge(7, 11, 1);
    g.uedge(7, 10, 1);
    g.uedge(8, 9, 1);
    g.uedge(8, 11, 1);
    g.uedge(8, 10, 1);
    g.uedge(9, 11, 1);
    g.uedge(9, 10, 1);
    g
}
/// An exeample of a directed graph as a 2 structure.
/// From: Chrisophe Paul's HDR, http://www.lirmm.fr/%7Epaul/HdR/hdr.pdf
pub fn digraph_ex1() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.edge(1, 2, 1);
    g.edge(1, 3, 1);
    g.edge(2, 3, 1);
    g.edge(4, 1, 1);
    g.edge(4, 2, 1);
    g.edge(4, 3, 1);
    g.edge(4, 6, 1);
    g.edge(5, 1, 1);
    g.edge(5, 2, 1);
    g.edge(5, 3, 1);
    g.edge(5, 6, 1);
    g.edge(6, 4, 1);
    g.edge(6, 5, 1);
    g.edge(6, 7, 1);
    g.edge(6, 8, 1);
    g.edge(7, 8, 1);
    g.edge(8, 7, 1);
    g
}

pub fn linear_ex() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.edge(1, 2, 1);
    g.edge(1, 3, 1);
    g.edge(2, 3, 1);
    g
}

pub fn diamant_ex1() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.edge(1, 2, 1);
    g.edge(1, 3, 1);
    g.edge(1, 4, 1);
    g.edge(2, 4, 1);
    g.edge(3, 4, 1);
    g
}

pub fn sp_ex1() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 2..8 {
        g.edge(1, dst, 1);
    }
    g.edge(2, 7, 1);
    for dst in 4..8 {
        g.edge(3, dst, 1);
    }
    for dst in 6..8 {
        g.edge(4, dst, 1);
        g.edge(5, dst, 1);
    }
    g.edge(6, 7, 1);
    g
}

pub fn ex1() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 1..4 {
        g.edge(dst, 4, 1);
        g.edge(dst, 5, 1);
        g.edge(4, dst, 1);
        g.edge(5, dst, 1);
    }
    for dst in 6..10 {
        g.edge(dst, 4, 1);
        g.edge(dst, 5, 1);
        g.edge(4, dst, 1);
        g.edge(5, dst, 1);
    }
    g
}

pub fn ex2() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 1..4 {
        g.edge(dst, 4, 1);
        g.edge(dst, 5, 1);
        g.edge(4, dst, 1);
        g.edge(5, dst, 1);
    }
    for dst in 4..6 {
        g.edge(6, dst, 1);
        g.edge(8, dst, 1);
        g.edge(dst, 7, 1);
        g.edge(dst, 9, 1);
    }
    g
}

pub fn graph5() -> TwoStructure {
    let mut g = TwoStructure::new();
    for src in 0..5 {
        for dst in src+1..5 {
            g.edge(src, dst, 1);
        }
    }
    g
}

pub fn graph5c() -> TwoStructure {
    let mut g = TwoStructure::new();
    for src in 0..5 {
        for dst in src+1..5 {
            g.edge(src, dst, 1);
            g.edge(dst, src, 1);
        }
    }
    g
}

pub fn graph5_1() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 0..5 {
        g.edge(0, dst, 1);
    }
    g.edge(1, 0, 1);
    g.edge(1, 2, 1);
    for dst in 1..5 {
        g.edge(2, dst, 1);
    }
    g.edge(3, 2, 1);
    g.edge(3, 0, 1);
    g.edge(3, 4, 1);

    g.edge(4, 2, 1);
    g.edge(4, 0, 1);
    g.edge(4, 3, 1);

    g
}

pub fn graph5_1c() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 0..5 {
        g.edge(0, dst, 1);
        g.edge(dst, 0, 1);
    }
    g.edge(1, 0, 1);
    g.edge(1, 2, 1);
    g.edge(0, 1, 1);
    g.edge(2, 1, 1);
    for dst in 1..5 {
        g.edge(3, dst, 1);
        g.edge(dst, 2, 1);
    }

    g.edge(3, 2, 1);
    g.edge(3, 0, 1);
    g.edge(3, 4, 1);
    g.edge(2, 3, 1);
    g.edge(0, 3, 1);
    g.edge(4, 3, 1);

    g.edge(4, 2, 1);
    g.edge(4, 0, 1);
    g.edge(4, 3, 1);
    g.edge(2, 4, 1);
    g.edge(0, 4, 1);
    g.edge(3, 4, 1);

    g
}

pub fn graph5_2c() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 1..5 {
        g.edge(0, dst, 1);
    }
    g.edge(1, 0, 1);
    g.edge(1, 2, 1);

    g.edge(2, 1, 1);
    g.edge(2, 1, 1);
    g.edge(2, 3, 1);

    g.edge(3, 0, 1);
    g.edge(3, 2, 1);
    g.edge(3, 4, 1);

    g.edge(4, 0, 1);
    g.edge(4, 3, 1);

    g
}

pub fn graph5_2() -> TwoStructure {
    let mut g = TwoStructure::new();
    for dst in 1..5 {
        g.edge(0, dst, 1);
    }
    g.edge(1, 2, 1);
    g.edge(2, 3, 1);
    g.edge(4, 0, 1);
    g.edge(3, 4, 1);

    g
}

pub fn graph5_2_1() -> TwoStructure {
    let mut g = TwoStructure::new();

    g.edge(0, 1, 1);
    g.edge(0, 3, 1);
    g.edge(0, 4, 1);

    g.edge(1, 2, 1);
    g.edge(1, 4, 1);

    g.edge(2, 3, 1);

    g.edge(3, 4, 1);
    g.edge(4, 0, 1);
    g.edge(4, 1, 1);
    g.edge(4, 3, 1);

    g
}

pub fn graph_line1() -> TwoStructure {
    let mut g = TwoStructure::new();

    g.edge(0, 1, 1);
    g.edge(1, 2, 1);
    g.edge(2, 3, 1);

    g.edge(1, 0, 1);
    g.edge(2, 1, 1);
    g.edge(3, 2, 1);

    g
}

pub fn graph_line2() -> TwoStructure {
    let mut g = TwoStructure::new();

    g.edge(0, 1, 1);
    g.edge(1, 2, 1);
    g.edge(2, 3, 1);

    g
}

pub fn graph_line3() -> TwoStructure {
    let mut g = TwoStructure::new();

    for src in 0..4 {
        for dst in src+1..4 {
            g.edge(src, dst, 1);
        }
    }

    g
}

pub fn graph5_2_1c() -> TwoStructure {
    let mut g = TwoStructure::new();

    g.edge(0, 1, 1);
    g.edge(0, 3, 1);
    g.edge(0, 4, 1);

    g.edge(1, 0, 1);
    g.edge(1, 2, 1);
    g.edge(1, 4, 1);

    g.edge(2, 1, 1);
    g.edge(2, 3, 1);

    g.edge(3, 0, 1);
    g.edge(3, 2, 1);
    g.edge(3, 4, 1);

    g.edge(4, 0, 1);
    g.edge(4, 1, 1);
    g.edge(4, 3, 1);

    g
}

pub fn graph5_3c() -> TwoStructure {
    let mut g = TwoStructure::new();

    g.edge(0, 1, 1);
    g.edge(0, 3, 1);
    g.edge(0, 4, 1);

    g.edge(1, 0, 1);
    g.edge(1, 2, 1);

    g.edge(2, 1, 1);
    g.edge(2, 3, 1);

    g.edge(3, 2, 1);
    g.edge(3, 4, 1);
    g.edge(3, 0, 1);

    g.edge(4, 0, 1);
    g.edge(4, 3, 1);

    g
}

pub fn g19_3__1() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 6..10 {
        g.edge(0, i, 1);
        g.edge(i, 0, 1);
    }
    for i in 6..10 {
        for j in i+1..10 {
            g.edge(i, j, 1);
            g.edge(j, i, 1);
        }
    }

    g.edge(9, 1, 1);
    g.edge(1, 9, 1);
    g.edge(1, 2, 1);
    g.edge(2, 3, 1);
    g.edge(3, 4, 1);
    g.edge(3, 5, 1);
    g.edge(4, 5, 1);

    g
}

pub fn g20_3__linear1() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 0..10 {
        for j in i+1..10 {
            g.edge(i, j, 1);
        }
    }
    g
}

pub fn g20_3__linear2() -> TwoStructure {
    let mut g = TwoStructure::new();

    for i in 6..10 {
        g.edge(5, i, 1);
    }
    for i in 7..10 {
        g.edge(6, i, 1);
    }
    for i in 8..10 {
        g.edge(7, i, 1);
    }
    for i in 9..10 {
        g.edge(8, i, 1);
    }

    for i in 1..10 {
        g.edge(0, i, 1);
    }
    for i in 2..10 {
        g.edge(1, i, 1);
    }
    for i in 3..10 {
        g.edge(2, i, 1);
    }
    for i in 4..10 {
        g.edge(3, i, 1);
    }
    for i in 5..10 {
        g.edge(4, i, 1);
    }

    g
}

pub fn g20_3() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.edge(0, 1, 1);
    g.edge(1, 0, 1);
    g.edge(0, 1, 6);
    g.edge(0, 1, 1);
    for i in 1..6 {
        for j in i+1..6 {
            g.edge(i, j, 1);
            g.edge(j, i, 1);
        }
    }
    for i in 6..10 {
        for j in i+1..10 {
            g.edge(i, j, 1);
        }
    }
    g
}

pub fn g20_complete() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 0..5 {
        for j in i+1..5 {
            g.edge(i, j, 1);
            g.edge(j, i, 1);
        }
    }
    g
}

pub fn g20_prime() -> TwoStructure {
    let mut g = TwoStructure::new();

    for i in 0..5 {
        g.edge(i, i+1, 1);
    }

    g
}

pub fn g22_3_complete_linear() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 0..3 {
        for j in i+1..3 {
            g.edge(i, j, 1);
            g.edge(j, i, 1);
        }
    }
    for i in 2..5 {
        for j in i+1..5 {
            g.edge(i, j, 1);
        }
    }

    g
}

pub fn g22_3_lcl() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 0..6 {
        for j in i+1..6 {
            g.edge(i, j, 1);
        }
    }
    for i in 3..6 {
        for j in i+1..6 {
            g.edge(j, i, 1);
        }
    }
    for i in 3..9 {
        for j in 6..9 {
            g.edge(i, j, 1);
        }
    }
    g
}

pub fn g22_3_2() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 1..6 {
        g.edge(0, i, 1);
    }
    for i in 2..6 {
        g.edge(1, i, 1);
    }
    for i in 3..6 {
        g.edge(2, i, 1);
    }
    for i in 4..6 {
        g.edge(3, i, 1);
    }
    g.edge(4, 5, 1);
    g.edge(3, 2, 1);
    g
}

pub fn g22_3_3() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 1..6 {
        g.edge(0, i, 1);
    }
    for i in 2..6 {
        g.edge(1, i, 1);
    }
    for i in 4..6 {
        g.edge(2, i, 1);
    }
    for i in 4..6 {
        g.edge(3, i, 1);
    }
    g.edge(4, 5, 1);
    g.edge(3, 2, 1);
    g
}

pub fn g22_3_4() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 1..6 {
        g.edge(0, i, 1);
    }
    for i in 2..6 {
        g.edge(1, i, 1);
    }
    for i in 4..6 {
        g.edge(2, i, 1);
    }
    for i in 4..6 {
        g.edge(3, i, 1);
    }
    g.edge(4, 5, 1);
    g.edge(3, 6, 1);
    g.edge(6, 2, 1);
    g
}

pub fn g22_3_5() -> TwoStructure {
    let mut g = TwoStructure::new();
    for i in 1..6 {
        g.edge(0, i, 1);
    }
    for i in 2..6 {
        g.edge(1, i, 1);
    }
    for i in 4..6 {
        g.edge(2, i, 1);
    }
    for i in 4..6 {
        g.edge(3, i, 1);
    }
    g.edge(4, 5, 1);
    g.edge(3, 6, 1);
    g.edge(6, 2, 1);
    for i in 0..3 {
        g.edge(i, 6, 1);
    }
    g
}


// module de test

#[cfg(test)]
mod tests {
    // use core::panicking::panic;
    use std::fs::File;
    use std::io::Write;
    use std::path::Path;
    use crate::two_structure::*;

    // #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }

    // #[test]
    fn test01() {
        let g = linear_ex();
        for color in 0..g.colors.len() {
            println!("edges with color {}:", color as u64);
            // for edges in g.colors.get(color) {
            if let Some(edges) = g.colors.get(color) {
                for &edge in edges {
                    println!("{} -> {}", edge.0, edge.1);
                }
            }
            println!();
        }
        println!();
    }

    // #[test]
    fn test_graph_ex1() {
        let path = Path::new("files/graph_ex1.dot");
        let display = path.display();

        // Open file in write-only mode
        let mut file = match File::create(&path) {
            Err(why) => panic!("couldn't create {}: {}", display, why),
            Ok(file) => file,
        };

        let mut g = graph_ex1();

        let graph_ex1_dot = g.to_dot(false, false);

        // Write the graph_ex1 dot string to 'file'
        match file.write_all(graph_ex1_dot.as_bytes()) {
            Err(why) => panic!("couldn't write to {}: {}", display, why),
            Ok(_) => println!("successfully wrote to {}", display),
        }

        // test number of nodes
        assert_eq!(g.nodes.len() as u64, 11);
        // test number of all edges
        let all_edges_g = g.all_edges();
        assert_eq!(all_edges_g.len() as u64, 110);

        let mut num_color = 0;

        // number of edges with color 0
        for (_, _, color) in all_edges_g.clone() {
            if color == 0 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 52);

        // number of edges with color 1
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 1 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 58);

        // number of edges with color 2
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 2 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 0);
    }

    // #[test]
    fn test_digraph_ex1() {
        let path = Path::new("files/digraph_ex1.dot");
        let display = path.display();

        // Open file in write-only mode
        let mut file = match File::create(&path) {
            Err(why) => panic!("couldn't create {}: {}", display, why),
            Ok(file) => file,
        };

        let mut g = digraph_ex1();

        let digraph_ex1_dot = g.to_dot(false, false);

        // Write the digraph_ex1 dot string to 'file'
        match file.write_all(digraph_ex1_dot.as_bytes()) {
            Err(why) => panic!("couldn't write to {}: {}", display, why),
            Ok(_) => println!("successfully wrote to {}", display),
        }

        // test number of nodes
        assert_eq!(g.nodes.len() as u64, 8);
        // test number of all edges
        let all_edges_g = g.all_edges();
        assert_eq!(all_edges_g.len() as u64, 56);

        let mut num_color = 0;

        // number of edges with color 0
        for (_, _, color) in all_edges_g.clone() {
            if color == 0 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 39);

        // number of edges with color 1
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 1 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 17);

        // number of edges with color 2
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 2 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 0);
    }

    // #[test]
    fn test_linear_ex() {
        let path = Path::new("files/linear_ex.dot");
        let display = path.display();

        // Open file in write-only mode
        let mut file = match File::create(&path) {
            Err(why) => panic!("couldn't create {}: {}", display, why),
            Ok(file) => file,
        };

        let mut g = linear_ex();

        let linear_ex_dot = g.to_dot(false, false);

        // Write the linear_ex dot string to 'file'
        match file.write_all(linear_ex_dot.as_bytes()) {
            Err(why) => panic!("couldn't write to {}: {}", display, why),
            Ok(_) => println!("successfully wrote to {}", display),
        }

        // test number of nodes
        assert_eq!(g.nodes.len() as u64, 3);
        // test number of all edges
        let all_edges_g = g.all_edges();
        assert_eq!(all_edges_g.len() as u64, 6);

        let mut num_color = 0;

        // number of edges with color 0
        for (_, _, color) in all_edges_g.clone() {
            if color == 0 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 3);

        // number of edges with color 1
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 1 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 3);

        // number of edges with color 2
        num_color = 0;
        for (_, _, color) in all_edges_g.clone() {
            if color == 2 {
                num_color += 1;
            }
        }
        assert_eq!(num_color, 0);
    }
}



pub fn graph_ex2() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.uedge(1, 2, 1);
    g.uedge(1, 3, 1);
    g.uedge(1, 4, 1);
    g.uedge(1, 5, 1);
    g.uedge(2, 3, 1);
    g.uedge(2, 4, 1);
    g.uedge(2, 6, 1);
    g.uedge(3, 4, 1);
    g.uedge(3, 7, 1);
    g.uedge(4, 5, 1);
    g.uedge(4, 6, 1);
    g.uedge(5, 6, 1);
    g.uedge(5, 7, 1);
    g.uedge(6, 7, 1);
    g.uedge(6, 8, 1);
    g.uedge(7, 8, 1);
    g.uedge(8, 9, 1);
    g.uedge(8, 10, 1);
    g.uedge(9, 10, 1);
    g.uedge(10, 11, 1);
    g.uedge(9, 11, 1);
    g
}

pub(crate) fn graph_ex3() -> TwoStructure {
    let mut g = TwoStructure::new();
    g.uedge(1, 2, 1);
    g.uedge(1, 3, 1);
    g.uedge(2, 4, 1);
    g.uedge(2, 5, 1);
    g.uedge(3, 6, 1);
    g.uedge(3, 7, 1);
    g.uedge(4, 8, 1);
    g.uedge(5, 9, 1);
    g.uedge(6, 10, 1);
    g.uedge(7, 11, 1);
    g.uedge(8, 12, 1);
    g.uedge(9, 12, 1);
    g.uedge(10, 12, 1);
    g.uedge(11, 12, 1);
    g.uedge(1, 12, 1);
    g
}

fn generate_graph(num_edges: usize) -> TwoStructure {
    let mut g = TwoStructure::new();
    let mut rng = rand::thread_rng();
    while g.colors[1].len() < num_edges {
        let src = rng.gen_range(1..=100);
        let dst = rng.gen_range(1..=100);
        if src != dst {
            g.edge(src, dst, 1);
        }
    }
    g
}

pub fn graph_50_100() -> TwoStructure {
    generate_graph(50)
}
