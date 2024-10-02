// strongly connected components
// (Tarjan algorithm)

use std::cell::RefCell;
use std::cmp::min;
use std::collections::HashMap;
use std::collections::HashSet;

pub trait GraphTrait {
    fn vertices(&self) -> HashSet<u64>;
    fn successors(&mut self, v: u64) -> Option<&HashSet<u64>>;
}

#[derive(Debug)]
pub struct MiniGraph {
    dico: HashMap<u64, HashSet<u64>>,
}

impl Clone for MiniGraph {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl MiniGraph {
    pub fn new(dico: HashMap<u64, HashSet<u64>>) -> MiniGraph {
        MiniGraph { dico }
    }
}

impl GraphTrait for MiniGraph {
    fn vertices(&self) -> HashSet<u64> {
        let mut result: HashSet<u64> = HashSet::new();
        for key in self.dico.keys() {
            result.insert(*key);
        }
        result
    }

    fn successors(&mut self, v: u64) -> Option<&HashSet<u64>> {
        self.dico.get(&v)
    }
}

#[derive(Clone, Copy)]
pub struct SCCNode {
    // original vertex ... must be hashable and unique (among vertices)
    pub vertex: u64,
    pub index: u64,
    pub lowlink: u64,
    pub on_stack: bool,
}

// representation of a graph node
impl SCCNode {
    pub fn new(vertex: u64, index: u64) -> SCCNode {
        SCCNode {
            vertex,
            index,
            lowlink: index,
            on_stack: false,
        }
    }
}

impl PartialEq for SCCNode {
    fn eq(&self, other: &Self) -> bool {
        (self.vertex == other.vertex)
            && (self.index == other.index)
            && (self.lowlink == other.lowlink)
    }
}

// #[derive(Debug)]
pub struct SCC<'a> {
    pub graph: Box<dyn GraphTrait + 'a>,
    pub index: u64,
    pub components: Vec<HashSet<u64>>,
    pub comp_index: u64,
    pub dfs_stk: Vec<SCCNode>,
    pub visited: HashMap<u64, SCCNode>,
}

impl<'a> Clone for SCC<'a>
{
    fn clone(&self) -> Self {
        todo!()
    }
}


impl<'a> SCC<'a>
{
    pub fn new(graph: Box<dyn GraphTrait + 'a>) -> SCC<'a> {
        SCC {
            graph,
            index: 0,
            components: Vec::new(),
            comp_index: 0,
            dfs_stk: Vec::new(),
            visited: HashMap::new(),
        }
    }


    pub fn compute(&mut self) {
        for v in self.graph.vertices() {
            if self.visited.contains_key(&v) {
                continue;
            }
            // v has not been visited
            let mut vnode = SCCNode::new(v, self.index);
            self.index += 1;
            vnode.on_stack = true;
            self.visited.insert(v, vnode);
            vnode.on_stack = false;
            // println!("126: [compute | node selected for visit] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
            self.visit(&RefCell::new(vnode));
        }
    }

    pub fn visit(&mut self, node: &RefCell<SCCNode>) -> SCCNode {
        let mut vnode = node.borrow_mut();
        // println!("133: [visit | enter on visit] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
        vnode.on_stack = true;
        self.dfs_stk.push(*vnode);
        // println!("136: [visit | set on_stack with true] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);

        // let mut nhs = HashSet::new();
        // for w in self.graph.dico.remove(&vnode.vertex).unwrap().into_iter() {
        let s = self.graph.successors(vnode.vertex);
        match s {
            Some(h) => {
                for w in h.clone() {
                    // println!("141: [visit | select successor] w select for successors of SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {}) is {}", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack, w);
                    // nhs.insert(w);
                    if !self.visited.contains_key(&w) {
                        // recurse
                        let mut wnode = SCCNode::new(w, self.index);
                        self.index += 1;
                        wnode.on_stack = true;
                        self.visited.insert(w, wnode);
                        wnode.on_stack = false;
                        // println!("150: [visit | wnode before visit] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", wnode.vertex, wnode.index, wnode.lowlink, wnode.on_stack);
                        wnode = self.visit(&RefCell::new(wnode));
                        // println!("152: [visit | wnode after visit] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", wnode.vertex, wnode.index, wnode.lowlink, wnode.on_stack);
                        // println!("153: [visit | vnode value] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
                        vnode.lowlink = min(vnode.lowlink, wnode.lowlink);
                        // println!("155: [visit | vnode after set lowlink] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
                    } else {
                        let wnode = self.visited.get(&w).unwrap();
                        // println!("158: [visit | w is visited] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", wnode.vertex, wnode.index, wnode.lowlink, wnode.on_stack);
                        if wnode.on_stack {
                            vnode.lowlink = min(vnode.lowlink, wnode.index);
                        }
                        // println!("162: [visit | vnode after set lowlink] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
                    }
                }
                // self.graph.dico.insert(vnode.vertex, nhs);

                // println!("168: [visit | out of for successors] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", vnode.vertex, vnode.index, vnode.lowlink, vnode.on_stack);
                if vnode.lowlink == vnode.index {
                    let mut component = HashSet::new();
                    loop {
                        let mut wnode = self.dfs_stk.pop().unwrap();
                        // println!("173: [visit | wnode in dfs_stk.pop] SCCNode(vertex: {}, index: {}, lowlink: {}, on_stack: {})", wnode.vertex, wnode.index, wnode.lowlink, wnode.on_stack);
                        wnode.on_stack = false;
                        self.visited.get_mut(&(wnode.vertex)).unwrap().on_stack = false;
                        component.insert(wnode.vertex);
                        // if wnode is vnode
                        if wnode.vertex == vnode.vertex {
                            break;
                        }
                    }

                    self.components.push(component);
                }
            }
            _ => {}
        }

        *vnode
    }
}


pub fn strongly_connected_components(graph: Box<dyn GraphTrait>) -> Vec<HashSet<u64>> {
    // Compute the strongly connected components of 'graph'
    // The graph must have a 'vertice()' iterator
    // as well as a 'successors(v)' iterator for the successors
    // of vertex 'v' in the graph.
    // Returns a list of sets of vertices.
    let mut scc = SCC::new(graph);
    scc.compute();
    scc.components
}

pub fn diagraph_ex1() -> MiniGraph {
    let hm: HashMap<u64, HashSet<u64>> = HashMap::from([
        (1, HashSet::from([2])),
        (2, HashSet::from([3])),
        (3, HashSet::from([1])),
        (4, HashSet::from([2, 3, 5])),
        (5, HashSet::from([4, 6])),
        (6, HashSet::from([3, 7])),
        (7, HashSet::from([7, 6])),
        (8, HashSet::from([5, 7, 8])),
    ]);

    let g = MiniGraph::new(hm);
    g
}

pub fn test_scc() {
    let results = strongly_connected_components(Box::new(diagraph_ex1()));
    println!("[");
    for r in results {
        print!("{{");
        for element in r {
            print!(" {} ", element);
        }
        println!("}}");
    }
    println!("]");
}
