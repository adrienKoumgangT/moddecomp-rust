// use std::hash::{Hash, Hasher};
// use std::ops::Deref;


pub mod moddecomp {
    // use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};
    use std::fmt::format;
    use std::fs::File;
    use std::io;
    use std::io::{Read, Write};
    use std::time::Instant;
    use crate::scc::{GraphTrait, strongly_connected_components};
    use crate::two_structure::{graph_ex1, TwoStructure, node_to_str, node_to_str2};

    #[derive(Eq, Hash)]
    enum TAG {
        VALUE,
        OTHER
    }


    impl PartialEq for TAG {
        fn eq(&self, other: &Self) -> bool {
            match self {
                TAG::VALUE => {
                    match other {
                        TAG::VALUE => true,
                        TAG::OTHER => false
                    }
                }
                TAG::OTHER => {
                    match other {
                        TAG::VALUE => false,
                        TAG::OTHER => true
                    }
                }
            }
        }
    }

    #[derive(Eq)]
    struct DecompositionGraph {
        tag: TAG,
        value: u64,
        name: String,
        list_value: Vec<DecompositionGraph>
    }

    impl PartialEq<Self> for DecompositionGraph {
        fn eq(&self, other: &Self) -> bool {
            return match self.tag {
                TAG::VALUE => {
                    if other.tag == TAG::VALUE {
                        self.value == other.value
                    } else {
                        false
                    }
                }
                TAG::OTHER => {
                    if other.tag == TAG::OTHER {
                        self.name == other.name && self.list_value.len() == other.list_value.len()
                    } else {
                        false
                    }
                }
            }
        }
    }

    /*
    impl Hash for DecompositionGraph {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state);
            self.name.hash(state);
            self.list_value.hasher();
        }
    }
    */

    impl DecompositionGraph {
        pub fn new(tag: TAG, value: u64, name: String) -> Self {
            Self {
                tag,
                value,
                name,
                list_value: Vec::new()
            }
        }

        pub fn print(&self) {
            match self.tag {
                TAG::VALUE => {
                    print!("{}", self.value);
                }
                TAG::OTHER => {
                    print!("({}, [", self.name);
                    for dg in &self.list_value {
                        dg.print();
                    }
                    print!("])");
                }
            }
        }
    }

    pub fn pickup_in_hashset<T: Clone>(set: &HashSet<T>) -> T {
        set.iter().next().unwrap().clone()
    }

    pub fn pickup_in_set<T: Clone>(set: &Vec<T>) -> T {
        set.iter().next().unwrap().clone()
    }

    pub fn distinguish(/*mut*/ g: &mut TwoStructure, w: u64, v1: u64, v2: u64) -> bool {
        // returns true if w distinguishes v1 and v2 in two structure g
        // let mut g = graph.borrow_mut();
        let w_v1_col = g.color_of(w, v1);
        if g.colors.get(w_v1_col as usize).unwrap().contains(&(w, v2)) ||
            (w_v1_col == 0 && g.color_of(w, v2) == 0) {
            let v1_w_col = g.color_of(v1, w);
            if g.colors.get(v1_w_col as usize).unwrap().contains(&(v2, w)) ||
                (v1_w_col == 0 && g.color_of(v2, w) == 0) {
                return false;
            }
        }
        true
    }

    /// Partitions module in strong maximal modules
    ///
    /// # Arguments
    ///
    /// * 'g' - a two-structure
    /// * 'w' - the first node used for partitioning module
    /// * 'module' - a set of nodes of g to partition
    ///
    /// # Returns
    ///
    /// a list of sets of nodes
    pub fn partition_module(/*mut*/ g: &mut TwoStructure, w: u64, module: HashSet<u64>) -> Vec<HashSet<u64>> {
        // let mut g = graph.borrow_mut();
        let colors_len = g.colors.len();

        // modules = [ [set() for c in g.colors] for c_ in g.colors ]
        let mut modules: Vec<Vec<HashSet<u64>>> = Vec::new();

        // is_empty = [ [True for c in g.colors] for c_ in g.colors ]
        let mut is_empty: Vec<Vec<bool>> = Vec::new();
        for _ in 0..colors_len {
            let mut vec_intern_modules_aux: Vec<HashSet<u64>> = Vec::new();
            let mut vec_intern_is_empty_aux: Vec<bool> = Vec::new();
            for _ in 0..colors_len {
                let /*mut*/ set_inter_modules_aux: HashSet<u64> = HashSet::new();
                vec_intern_modules_aux.push(set_inter_modules_aux);
                vec_intern_is_empty_aux.push(false);
            }
            modules.push(vec_intern_modules_aux);
            is_empty.push(vec_intern_is_empty_aux);
        }

        for n in module {
            let c_w_n = g.color_of(w, n); // first color
            let c_n_w = g.color_of(n, w); // second color

            modules.get_mut(c_w_n as usize).unwrap().get_mut(c_n_w as usize).unwrap().insert(n);

            if *is_empty.get(c_w_n as usize)
                .unwrap()
                .get(c_n_w as usize)
                .unwrap()
            {
                is_empty.get_mut(c_w_n as usize)
                    .unwrap()
                    .push(false);
            }
        }

        let mut flattened: Vec<HashSet<u64>> = Vec::new();
        for m in modules {
            for s in m {
                if !s.is_empty() {
                    flattened.push(s);
                }
            }
        }
        flattened
    }


    /// constructs M(g, v) according to the algorithm 3.1 of the article [1]
    ///
    /// # Arguments
    ///
    /// * 'g' - a two-structure
    /// * 'v' - a node of g
    ///
    /// # Returns
    ///
    /// a list of sets of nodes (modules)
    pub fn maximal_modules(/*mut*/ g: &mut TwoStructure, v: u64) -> Vec<HashSet<u64>> {
        // let mut g = graph.borrow_mut();
        let mut init_module = g.nodes.clone();
        init_module.remove(&v);
        let mut partition = Vec::new();
        partition.push(init_module);
        let mut outsiders = Vec::new();
        let mut outsiders_h = HashSet::new();
        outsiders_h.insert(v);
        outsiders.push(outsiders_h);
        // let mut module = HashSet::new();
        loop {
            if partition.is_empty() {
                panic!("Empty partition (please report)")
            }
            // module = None
            let mut module = HashSet::new();
            // println!("partition.len() = {}", partition.len());
            let mut index = 0;
            for i in 0..partition.len() {
                if outsiders.get(i).unwrap().len() as u64 > 0 {
                    // pick a module with outsiders
                    module = partition.get(i).unwrap().clone();
                    /*print!("module select is = {{");
                    let print_module = module.clone();
                    for e in print_module {
                        print!(" {} ", e);
                    }
                    println!(" }}");*/
                    index = i;
                    break;
                }
            }
            if module.is_empty() {
                // if there is no module left having outsiders
                return partition;
            }

            // partition.remove(module)
            for i in 0..partition.len() {
                if *partition.get(i).unwrap() == module {
                    partition.remove(i);
                    break;
                }
            }

            let /*mut*/ outsiders_i = outsiders.remove(index);
            // outsiders.remove(outsiders_i)


            // pick an arbitrary element
            let w = pickup_in_hashset(&outsiders_i);

            // list of sets of nodes
            let mut graph_alter = g.clone();
            let module_partition = module.clone();
            let /*mut*/ r_modules = partition_module(&mut graph_alter, w, module_partition);
            for r_module in r_modules {
                let /*mut*/ r_module_diff = r_module.clone();
                partition.push(r_module);
                // a = module - r_module
                let /*mut*/ ha_alter = module.clone();
                let /*mut*/ ha = ha_alter
                    .difference(&r_module_diff)
                    .collect::<HashSet<_>>();
                let mut a = HashSet::new();
                for &eha in ha {
                    a.insert(eha);
                }
                let mut b: HashSet<u64> = HashSet::new();
                if !outsiders_i.is_empty() {
                    for el in outsiders_i.iter() {
                        b.insert(*el);
                    }
                }
                b.remove(&w);
                outsiders.push(b);
            }
        }

        // this never happens
        // partition
    }


    // ADD 27/07/2024 --- from moddecomp

    fn build_quotient(g: &mut TwoStructure, mut partition: Vec<HashSet<u64>>, v: u64) -> TwoStructure {
        let mut qg = TwoStructure::new();
        partition.push(vec![v].into_iter().collect());
        qg.modules = partition;
        let mut representatives = Vec::new();
        for v in &qg.modules {
            // let iter = v.iter();
            // let cloned_set: HashSet<u64> = iter.cloned().collect();
            representatives.push(pickup_in_hashset(v));
        }
        // let representatives: Vec<u64> = qg.modules.iter().map(|u| pickup(*u.iter().cloned())).collect();

        for i in 0..representatives.len() as u64 {
            for j in 0..representatives.len() as u64 {
                if i != j {
                    let color = g.color_of(representatives[i as usize], representatives[j as usize]);
                    if color != 0 {
                        qg.edge(i, j, color);
                    }
                }
            }
        }
        qg.nodes = (0..representatives.len() as u64).collect();

        qg
    }

    fn repr_to_module(qg: &TwoStructure, r: u64) -> &HashSet<u64> {
        &qg.modules[r as usize]
    }

    #[derive(Debug)]
    #[derive(Clone)]
    pub(crate) struct DGraph {
        nodes: HashSet<u64>,
        edges: Vec<HashSet<u64>>,
        modules: Vec<HashSet<u64>>,
    }

    impl DGraph {
        fn new() -> Self {
            DGraph {
                nodes: HashSet::new(),
                edges: Vec::new(),
                modules: Vec::new(),
            }
        }

        fn edge(&mut self, src: u64, dst: u64) {
            self.nodes.insert(src);
            self.nodes.insert(dst);
            if self.edges.len() <= src as usize {
                self.edges.resize((src + 1) as usize, HashSet::new());
            }
            self.edges[src as usize].insert(dst);
        }

        fn remove_vertex(&mut self, v: u64) {
            self.nodes.remove(&v);
            if v < self.edges.len() as u64 {
                self.edges[v as usize] = HashSet::new();
            }
            for e in &mut self.edges {
                e.remove(&v);
            }
        }

        fn node_to_module(&self, node: u64) -> &HashSet<u64> {
            &self.modules[node as usize]
        }

        fn to_dot(&self) -> String {
            let mut dot = String::from("digraph {\n  // nodes\n");
            let mut nodemap = HashMap::new();
            let mut vid = 1;
            for &node in &self.nodes {
                nodemap.insert(node, vid);
                dot.push_str(&format!(
                    "  N{} [label=\"{}\"];\n",
                    vid,
                    node_to_str2(self.node_to_module(node))
                ));
                vid += 1;
            }
            dot.push_str("\n  // edges\n");
            for (src, dsts) in self.edges.iter().enumerate() {
                for &dst in dsts {
                    dot.push_str(&format!("  N{} -> N{};\n", nodemap[&(src as u64)], nodemap[&dst]));
                }
            }
            dot.push_str("\n}\n");
            dot
        }
    }

    impl GraphTrait for DGraph {
        fn vertices(&self) -> HashSet<u64> {
            self.nodes.clone()
        }

        fn successors(&mut self, v: u64) -> Option<&HashSet<u64>> {
            self.edges.get(v as usize)
        }
    }

    fn build_distinction_graph(qg: &mut TwoStructure, w: u64) -> DGraph {
        let mut dg = DGraph::new();
        dg.modules = qg.modules[..qg.modules.len() - 1].to_vec();
        let w = (qg.modules.len() - 1) as u64;
        dg.nodes = qg.nodes.difference(&vec![w].into_iter().collect()).cloned().collect();
        let iter1 = dg.nodes.iter();
        let n1: HashSet<u64> = iter1.cloned().collect();
        let iter2 = dg.nodes.iter();
        let n2: HashSet<u64> = iter2.cloned().collect();
        for &src in &n1 {
            for &dst in &n2 {
                if src != w && dst != w && distinguish(qg, src, dst, w) {
                    dg.edge(src, dst);
                }
            }
        }
        dg
    }

    fn component_to_str(dg: &DGraph, comp: &HashSet<u64>) -> String {
        let mut s = String::from("{");
        let mut virg = false;
        for &nodes in comp {
            if virg {
                s.push_str(", ");
            }
            s.push_str(&node_to_str2(dg.node_to_module(nodes)));
            virg = true;
        }
        s.push('}');
        s
    }


    #[derive(Debug)]
    struct ComponentGraph {
        graph: DGraph,
        components: Vec<HashSet<u64>>,
        modules: Vec<HashSet<u64>>,
    }

    impl ComponentGraph {
        fn new(graph: DGraph) -> Self {
            let components = strongly_connected_components(Box::new(graph.clone()));
            let modules = graph.modules.clone();
            ComponentGraph { graph, components, modules }
        }

        fn node_to_module(&self, comp: u64) -> &HashSet<u64> {
            &self.modules[comp as usize]
        }

        fn is_sink(&mut self, component: HashSet<u64>) -> bool {
            let c = component.clone();
            for node in c {
                let s = self.graph.successors(node);
                match s {
                    Some(v) => {
                        for &successor in v {
                            if !component.contains(&successor) {
                                return false;
                            }
                        }
                    }
                    _ => {}
                }
            }
            true
        }

        fn remove_component(&mut self, comp: &HashSet<u64>) {
            for &node in comp {
                self.graph.remove_vertex(node);
            }
        }

        fn remove_sinks(&mut self) -> Vec<HashSet<u64>> {
            let mut sinks = Vec::new();
            let mut ncomps = Vec::new();
            let cts = self.components.clone();
            for comp in cts {
                let c = comp.clone();
                if self.is_sink(comp) {
                    sinks.push(c);
                } else {
                    ncomps.push(c);
                }
            }

            for comp in &sinks {
                self.remove_component(comp);
            }

            self.components = ncomps;
            sinks
        }

        fn is_empty(&self) -> bool {
            self.components.is_empty()
        }

        fn to_dot(&mut self) -> String {
            let mut dot = String::from("digraph {\n  //components\n");
            let mut cid = 1;
            let mut nodemap = HashMap::new();

            for comp in &self.components {
                dot.push_str(&format!(
                    "  C{} [label=\"{}\"];\n",
                    cid,
                    component_to_str(&self.graph, comp)
                ));
                for &node in comp {
                    nodemap.insert(node, cid);
                }
                cid += 1;
            }

            dot.push_str("\n  //edges\n");
            let mut edgemap = HashMap::new();
            let iter = self.graph.nodes.iter();
            let cloned_set: HashSet<u64> = iter.cloned().collect();

            for src in cloned_set {
                let s = self.graph.successors(src);
                match s {
                    Some(v) => {
                        for &dst in v {
                            let csrc = nodemap[&src];
                            let cdst = nodemap[&dst];
                            if !edgemap.entry(csrc).or_insert_with(HashSet::new).contains(&cdst) {
                                edgemap.get_mut(&csrc).unwrap().insert(cdst);
                                dot.push_str(&format!("  C{} -> C{};\n", csrc, cdst));
                            }
                        }
                    }
                    _ => {}
                }
            }

            dot.push_str("\n}\n");
            dot
        }
    }

    fn indent(level: usize, spaces: usize) -> String {
        " ".repeat(level * spaces)
    }

    #[derive(Debug)]
    pub enum Decomp {
        Leaf(Option<u64>),
        Node(String, Vec<Decomp>),
    }

    #[derive(Debug)]
    #[derive(Clone)]
    pub struct TreeNode {
        node_type: String,
        node_colors: Vec<u64>,
        children: Vec<TreeNode>,
        node_id: Option<u64>,
        prime_graph: Option<TwoStructure>,
        quotient: Option<TwoStructure>,
    }

    impl TreeNode {
        fn new(node_type: &str) -> Self {
            TreeNode {
                node_type: node_type.to_string(),
                node_colors: Vec::new(),
                children: Vec::new(),
                node_id: None,
                prime_graph: None,
                quotient: None
            }
        }

        fn add_child(&mut self, tnode: TreeNode) {
            self.children.push(tnode);
        }

        pub fn tostr(&self, level: usize) -> String {
            let mut ret = indent(level, 4);
            ret.push_str(&self.node_type);
            ret.push('\n');
            for child in &self.children {
                ret.push_str(&indent(level, 4));
                ret.push_str("|-- ");
                ret.push_str(&child.tostr(level + 1));
            }
            ret.push('\n');
            ret
        }

        pub fn to_decomp(&self) -> Decomp {
            if self.node_type == "LEAF" {
                Decomp::Leaf(self.node_id)
            } else {
                let decomps = self.children.iter().map(|child| child.to_decomp()).collect();
                Decomp::Node(self.node_type.clone(), decomps)
            }
        }

        pub fn node_ids(&self) -> HashSet<u64> {
            if self.node_type == "LEAF" {
                return match self.node_id {
                    Some(value) => {
                        let mut r = HashSet::new();
                        r.insert(value);
                        r
                    }
                    None => HashSet::new(),
                };
            }
            self.children.iter().flat_map(|child| child.node_ids()).collect()
        }

        fn node_buckets(&self) -> Vec<HashSet<u64>> {
            if self.node_type == "LEAF" {
                panic!("Cannot ask for node buckets in leaves");
            }
            self.children.iter().map(|child| child.node_ids()).collect()
        }
    }

    fn search_prime_graphs(tree: &TreeNode) -> Vec<&TwoStructure> {
        if tree.node_type == "PRIME" {
            return vec![tree.prime_graph.as_ref().unwrap()];
        }
        tree.children.iter().flat_map(|child| search_prime_graphs(child)).collect()
    }

    fn compute_total_order(g: &TwoStructure) -> Vec<u64> {
        let iter = g.nodes.iter();
        let mut order: Vec<u64> = iter.cloned().collect();
        let mut node_ref = HashMap::new();
        for (i, &node) in order.iter().enumerate() {
            node_ref.insert(node, i);
        }

        for (src, dst, _) in g.all_edges_but_zero() {
            // if node_ref.contains_key(&src) && node_ref.contains_key(&dst) {
            let src_ref = node_ref[&src];
            let dst_ref = node_ref[&dst];
            if dst_ref < src_ref {
                order.swap(src_ref, dst_ref);
                node_ref.insert(src, dst_ref);
                node_ref.insert(dst, src_ref);
            }
            // }
        }

        order
    }

    pub fn modular_decomposition(g: &mut TwoStructure, total_order: Option<Vec<u64>>) -> TreeNode {
        if g.nodes.len() == 1 {
            let mut root = TreeNode::new("LEAF");
            // let iter = g.nodes.iter();
            // let cloned_set: HashSet<u64> = iter.cloned().collect();
            root.node_id = Some(pickup_in_hashset(&g.nodes));
            return root;
        }

        let mut total_order = match total_order {
            Some(mut order) => {
                order.retain(|n| g.nodes.contains(n));
                if order.is_empty() {
                    compute_total_order(g)
                } else {
                    order
                }
            }
            None => compute_total_order(g)
        };

        let mut v: u64;
        loop {
            v = pickup_in_set(&total_order);
            total_order.retain(|&n| n != v);
            if g.nodes.contains(&v) {
                break;
            }
        }

        let mods = maximal_modules(g, v);
        let mut qg = build_quotient(g, mods, v);
        let dg = build_distinction_graph(&mut qg, v);
        let mut cg = ComponentGraph::new(dg);

        let mut root = TreeNode::new("");
        // let mut u = &mut root;
        root.quotient = Some(qg.clone());
        let mut u = &mut root;

        while !cg.is_empty() {
            let mut w = TreeNode::new("LEAF");
            w.node_id = Some(v);
            let sinks = cg.remove_sinks();
            let mut fmodules: HashSet<u64> = HashSet::new();

            for sink in &sinks {
                for &mod_ in sink {
                    fmodules.insert(mod_);
                }
            }

            if sinks.len() == 1 && fmodules.len() > 1 {
                u.node_type = "PRIME".to_string();
                u.prime_graph = Some(qg.clone());
            } else {
                let x = pickup_in_hashset(&qg.node_to_module(pickup_in_hashset(&fmodules)).unwrap());
                if g.color_of(x, v) == g.color_of(v, x) {
                    u.node_type = "COMPLETE".to_string();
                    u.node_colors = vec![g.color_of(v, x)];
                } else {
                    u.node_type = "LINEAR".to_string();
                    u.node_colors = vec![g.color_of(x, v), g.color_of(v, x)];
                }
            }

            for fmod in fmodules {
                let mut fg = g.slice((*qg.node_to_module(fmod).unwrap()).clone());
                let dtree = modular_decomposition(&mut fg, Some(total_order.clone()));
                if (u.node_type == "COMPLETE" && dtree.node_type == "COMPLETE" && u.node_colors == dtree.node_colors)
                    || (u.node_type == "LINEAR" && dtree.node_type == "LINEAR" && u.node_colors == dtree.node_colors)
                {
                    u.children.extend(dtree.children);
                } else {
                    u.add_child(dtree);
                }
            }

            u.add_child(w);
            u = u.children.last_mut().unwrap();
        }
        root
    }


    fn reconstruct_prime_graph(dtree: &TreeNode, buckets: Option<Vec<HashSet<u64>>>) -> TwoStructure {
        let mut pg = TwoStructure::new();
        let buckets = buckets.unwrap_or_else(|| dtree.node_buckets());
        pg.modules = buckets.clone();
        let qg = dtree.prime_graph.as_ref().unwrap();
        for &(u, v) in &qg.colors[1] {
            let mut u_id = None;
            let mut v_id = None;
            for (i, b) in buckets.iter().enumerate() {
                let r1 = qg.node_to_module(u);
                match r1 {
                    Some(h) => {
                        if h.intersection(b).count() > 0 {
                            u_id = Some(i as u64);
                        }
                    }
                    _ => {}
                }
                let r2 = qg.node_to_module(v);
                match r2 {
                    Some(h) => {
                        if h.intersection(b).count() > 0 {
                            v_id = Some(i as u64);
                        }
                    }
                    _ => {}
                }
            }
            if let (Some(u_id), Some(v_id)) = (u_id, v_id) {
                if u_id != v_id {
                    pg.edge(u_id, v_id, 1);
                }
            }
        }
        pg
    }

    fn reconstruct_prime_graph_dict(dtree: &TreeNode, buckets: Option<Vec<HashSet<u64>>>) -> HashMap<u64, HashSet<u64>> {
        let mut pg = HashMap::new();
        let buckets = buckets.unwrap_or_else(|| dtree.node_buckets());
        let qg = dtree.prime_graph.as_ref().unwrap();
        for &(u, v) in &qg.colors[1] {
            let mut u_id = None;
            let mut v_id = None;
            for (i, b) in buckets.iter().enumerate() {
                let r1 = qg.node_to_module(u);
                match r1 {
                    Some(h) => {
                        if h.intersection(b).count() > 0 {
                            u_id = Some(i as u64);
                        }
                    }
                    _ => {}
                }
                let r2 = qg.node_to_module(v);
                match r2 {
                    Some(h) => {
                        if h.intersection(b).count() > 0 {
                            v_id = Some(i as u64);
                        }
                    }
                    _ => {}
                }
            }
            if let (Some(u_id), Some(v_id)) = (u_id, v_id) {
                if u_id != v_id {
                    pg.entry(u_id).or_insert_with(HashSet::new).insert(v_id);
                }
            }
        }
        pg
    }


    // #[test]
    pub fn distinguish_unit_test() {
        print!("test1");
        let mut tst1 = TwoStructure::new();
        tst1.edge(1, 2, 1);
        tst1.edge(1, 3, 1);
        print!("does 1 distinguish 2 and 3? (no) -> {} \n", distinguish(&mut tst1, 1, 2, 3));

        print!("tst2");
        let mut tst2 = TwoStructure::new();
        tst2.edge(2, 1, 1);
        tst2.edge(3, 1, 1);
        print!("does 1 distinguish 2 and 3? (no) -> {} \n", distinguish(&mut tst2, 1, 2, 3));

        print!("tst3");
        let mut tst3 = TwoStructure::new();
        tst3.edge(1, 2, 1);
        tst3.edge(3, 1, 1);
        print!("does 1 distinguish 2 and 3? (yes) -> {} \n", distinguish(&mut tst3, 1, 2, 3));

        print!("tst4");
        let mut tst4 = TwoStructure::new();
        tst4.edge(2, 1, 1);
        tst4.edge(1, 3, 1);
        print!("does 1 distinguish 2 and 3? (yes) -> {} \n", distinguish(&mut tst4, 1, 2, 3));

        print!("tst5");
        let mut tst5 = TwoStructure::new();
        tst5.edge(2, 3, 1);
        print!("does 1 distinguish 2 and 3? (no) -> {} \n", distinguish(&mut tst5, 1, 2, 3));

        print!("tst6");
        let mut tst6 = TwoStructure::new();
        tst6.edge(2, 3, 1);
        tst6.edge(1, 3, 1);
        print!("does 1 distinguish 2 and 3? (yes) -> {} \n", distinguish(&mut tst6, 1, 2, 3));

        print!("tst7");
        let mut tst7 = TwoStructure::new();
        tst7.edge(3, 2, 1);
        tst7.edge(3, 1, 1);
        print!("does 1 distinguish 2 and 3? (yes) - {} \n", distinguish(&mut tst7, 1, 2, 3));

        print!("tst8");
        let mut tst8 = TwoStructure::new();
        tst8.edge(1, 2, 1);
        tst8.edge(2, 3, 1);
        print!("does 1 distinguish 2 and 3? (yes) -> {} \n", distinguish(&mut tst8, 1, 2, 3));

        print!("tst9");
        let mut tst9 = TwoStructure::new();
        tst9.edge(2, 1, 1);
        tst9.edge(2, 3, 1);
        print!("does 1 distinguish 2 and 3? (yes) -> {} \n", distinguish(&mut tst9, 1, 2, 3));
    }

    // #[test]
    pub fn unit_test_partition_module() {
        let mut g = graph_ex1();
        let mut s = g.nodes.clone();
        s.remove(&1);
        let /*mut*/ p = partition_module(&mut g, 1, s);
        print!("[");
        for hs in p {
            print!("{{ ");
            for node in hs {
                print!("{} ", node);
            }
            print!("}} ");
        }
        print!("]")
    }

    fn test_partition_module(mut g: TwoStructure, a: u64, n: u128) -> u128 {
        // let mut g = graph_ex1();
        // let mut vec = vec![];
        let mut total_time = 0u128;

        for _ in 0..a {
            let mut s = g.nodes.clone();
            s.remove(&1);
            partition_module(&mut g, 1, s);
        }

        for _ in 0..n {
            let mut s = g.nodes.clone();
            s.remove(&1);
            let start = Instant::now();
            partition_module(&mut g, 1, s);
            let duration = start.elapsed().as_micros();
            total_time += duration;
            // vec.push(duration);
        }
        // print!("{:?}", vec);
        let avg = total_time/n;
        // print!("avg = {:?} microseconds", avg);
        return avg;
    }

    // #[test]
    pub fn unit_test_partition_module_stat() {
        let mut g = graph_ex1();
        test_partition_module(g, 100_000, 1_000_000);
    }

    pub fn unit_test_partition_module_stat_all_graph(a: u64, n: u128) {
        let list_g = vec![
            ("graph ex1", graph_ex1()),
            // ("digraph ex1", digraph_ex1()),
            // ("linear ex", linear_ex()),
            // ("diamant ex1", diamant_ex1()),
            // ("sp ex1", sp_ex1()),
            // ("ex1", ex1()),
            // ("ex2", ex2()),
            // ("graph5", graph5()),
            // ("graph5c", graph5c()),
            // ("graph5_1", graph5_1()),
            // ("graph5_1c", graph5_1c()),
            /*("graph5_2c", graph5_2c()),
            ("graph5_2", graph5_2()),
            ("graph5_2_1", graph5_2_1()),
            ("graphlin1", graph_line1()),
            ("graphlin2", graph_line2()),
            ("graphlin3", graph_line3()),
            ("graph5_2_1c", graph5_2_1c()),
            ("graph5_3c", graph5_3c()),
            ("g19_3__1", g19_3__1()),
            ("g20_3__linear1", g20_3__linear1()),
            ("g20_3__linear2", g20_3__linear2()),
            ("g20_3", g20_3()),
            ("g20_complete", g20_complete()),
            ("g22_3_complete_linear", g22_3_complete_linear()),
            ("g22_3_lcl", g22_3_lcl()),
            ("g22_3_2", g22_3_2()),
            ("g22_3_3", g22_3_3()),
            ("g22_3_4", g22_3_4()),
            ("g22_3_5", g22_3_5())*/
        ];

        let mut result_text = String::new();

        for (name, g) in list_g {
            let mut result_g_text = format!("name: {}\n", name);
            let r = test_partition_module(g, a, n);
            result_g_text.push_str(&format!("\t - ({}, {}) {}\n", a, n, r));
            result_g_text.push('\n');
            println!("{}", result_g_text);
            result_text.push_str(&result_g_text);
        }

        let filename = format!("files/result_{}.txt", n);
        let mut file = File::create(filename);
        file.expect("REASON").write_all(result_text.as_bytes()).expect("TODO: panic message");
    }

    // #[test]
    pub fn unit_test_partition_module_stat_all() {
        let test_value = vec![
            (1, 10), (10, 100), (100, 1000), (1000, 10000),
            (10000, 100000), (100000, 1000000)
        ];

        for (a, n) in &test_value {
            unit_test_partition_module_stat_all_graph(*a, *n);
        }
    }


    // #[test]
    pub fn unit_test_maximal_modules() {
        let mut g = graph_ex1();
        print!("all edges = {{");
        for edge in g.all_edges() {
            println!("({}, {}, {})", edge.0, edge.1, edge.2);
        }
        println!("}}");
        let /*mut*/ mod1 = maximal_modules(&mut g, 1);
        print!("maximal modules = [ ");
        for hs in mod1 {
            print!("{{ ");
            for node in hs {
                print!("{} ", node);
            }
            print!("}} ");
        }
        println!("]");
    }

    pub fn test_maximal_modules(a: u64, n: u128) {
        let mut g = graph_ex1();
        // let mut vec = vec![];
        let mut total_time = 0u128;

        for _ in 0..a {
            maximal_modules(&mut g, 1);
        }

        for _ in 0..n {
            let start = Instant::now();
            maximal_modules(&mut g, 1);
            let duration = start.elapsed().as_micros();
            total_time += duration;
            // vec.push(duration);
        }
        print!("avg = {:?} microseconds", total_time/n);
    }

    // #[test]
    pub fn unit_test_maximal_module_stat() {
        test_maximal_modules(10, 1000);
    }

    pub fn test_maximal_module(mut g: TwoStructure, a: u64, n: u128) -> u128 {
        // let mut g = graph_ex1();
        // let mut vec = vec![];
        let mut total_time = 0u128;

        for _ in 0..a {
            maximal_modules(&mut g, 1);
        }

        for _ in 0..n {
            let start = Instant::now();
            maximal_modules(&mut g, 1);
            let duration = start.elapsed().as_micros();
            total_time += duration;
            // vec.push(duration);
        }
        let avg = total_time/n;
        // print!("avg = {:?} microseconds", avg);
        return avg;
    }

    pub fn unit_test_maximal_module_stat_all_graph(a: u64, n: u128) {
        let list_g = vec![
            ("graph ex1", graph_ex1()),
            // ("graph ex2", graph_ex3()),
            // ("digraph ex1", digraph_ex1()),
            // ("linear ex", linear_ex()),
            // ("diamant ex1", diamant_ex1()),
            // ("sp ex1", sp_ex1()),
            // ("ex1", ex1()),
            // ("ex2", ex2()),
            // ("graph5", graph5()),
            // ("graph5c", graph5c()),
            // ("graph5_1", graph5_1()),
            // ("graph5_1c", graph5_1c()),
            /*("graph5_2c", graph5_2c()),
            ("graph5_2", graph5_2()),
            ("graph5_2_1", graph5_2_1()),
            ("graphlin1", graph_line1()),
            ("graphlin2", graph_line2()),
            ("graphlin3", graph_line3()),
            ("graph5_2_1c", graph5_2_1c()),
            ("graph5_3c", graph5_3c()),
            ("g19_3__1", g19_3__1()),
            ("g20_3__linear1", g20_3__linear1()),
            ("g20_3__linear2", g20_3__linear2()),
            ("g20_3", g20_3()),
            ("g20_complete", g20_complete()),
            ("g22_3_complete_linear", g22_3_complete_linear()),
            ("g22_3_lcl", g22_3_lcl()),
            ("g22_3_2", g22_3_2()),
            ("g22_3_3", g22_3_3()),
            ("g22_3_4", g22_3_4()),
            ("g22_3_5", g22_3_5())*/
        ];

        let mut result_text = String::new();

        for (name, g) in list_g {
            let mut result_g_text = format!("name: {}\n", name);
            let r = test_maximal_module(g, a, n);
            result_g_text.push_str(&format!("\t - ({}, {}) {}\n", a, n, r));
            result_g_text.push('\n');
            println!("{}", result_g_text);
            result_text.push_str(&result_g_text);
        }

        let filename = format!("files/result_max_{}.txt", n);
        let mut file = File::create(filename);
        file.expect("REASON").write_all(result_text.as_bytes()).expect("TODO: panic message");
    }
    // #[test]
    pub fn unit_test_maximal_module_stat_all() {
        let test_value = vec![
            (1, 10), (10, 100), (100, 1000), (1000, 10000),
            (10000, 100000), (100000, 1000000)
        ];

        for (a, n) in &test_value {
            unit_test_maximal_module_stat_all_graph(*a, *n);
        }
    }
}
