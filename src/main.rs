use std::fs::File;
use std::io;
use std::io::{Read, Write, Result};
use ::moddecomp::two_structure::TwoStructure;

pub mod two_structure;
pub mod scc;
pub mod moddecomp;
pub mod utility;

fn read_dot_file(filename: &str) -> Result<String> {
    let mut file = File::open(filename)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}


fn main() {
    println!("Hello, world!");

    let filename = "files/two_structure_undirected_nodes_1000_edges_100206.dot";
    let result_dot_content = read_dot_file(filename);
    let dot_content = result_dot_content.unwrap();
    
    let mut file = File::create("files/edges.txt");
    

    let mut ts = TwoStructure::from_dot(&dot_content);

    match file {
        Ok(mut f) => {
            for (i, color_set) in ts.colors.iter().enumerate() {
                for (a, b) in color_set {
                    writeln!(f, "({}, {}),", a, b).expect("TODO: panic message");
                }

                // println!("Color {}: {:?}", i, color_set);
            }
        }
        Err(_) => {}
    }

}
