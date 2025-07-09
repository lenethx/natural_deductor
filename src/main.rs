use formula::Formula;
use core::panic;
use std::{
    cmp::max, collections::{BTreeMap, BTreeSet, HashSet}, default, f32::consts::E, iter::Product, ops::{Add, Deref, Index, Mul, Neg, Shr}
};
mod formula; // WHAT????
use itertools::Itertools;

use crate::{proof_search_tree::ProofSearchTree, sequent::Sequent};

type NodeID = usize;
type RuleID = usize;

//type Clausule = BTreeSet<Formula>;
//type ClausuleSet = BTreeSet<Clausule>;

mod proof_search_tree;
mod sequent;

#[derive(Clone)]
struct Node {
    id: NodeID,
    parents: Vec<(NodeID, RuleID)>,
    possible_subproofs: Vec<Rule>, //children
    data: Sequent,
    state: NodeState,
    gendepth: u32, 
    depth:u32,
    next_expansion:u32,
}

impl Node {
    fn is_proven(&self)->bool {
        matches!(self.state, NodeState::ProvenBy(_))
    }
    fn is_redundant(&self)->bool {
        matches!(self.state, NodeState::Redundant)
    }
    fn is_unproved(&self)->bool {
        matches!(self.state, NodeState::RequiredBy(_))
    }
}

#[derive(PartialEq, Eq, Clone)]
enum NodeState {
    Redundant,
    ProvenBy(RuleID),
    RequiredBy(u32),
}



#[derive(Copy, Clone)]
enum Rule {
    Ax,
    AndE1(NodeID),
    AndE2(NodeID),
    AndI(NodeID, NodeID),
    ImpI(NodeID),
    ImpE(NodeID, NodeID),
    OrI1(NodeID),
    OrI2(NodeID),
    OrE(NodeID, NodeID, NodeID),
    BotE(NodeID),
    NegE(NodeID, NodeID),
    NegI(NodeID),
    NegNegI(NodeID),
    MT(NodeID, NodeID),
    LEM,
    NegNegE(NodeID),
    PBC(NodeID),
}

#[derive(Default)]
struct BannedRules {
    ax:bool,
    andE1:bool,
    andE2:bool,
    andI:bool,
    impI:bool,
    impE:bool,
    orI1:bool,
    orI2:bool,
    orE:bool,
    botE:bool,
    negE:bool,
    negI:bool,
    negNegI:bool,
    MT:bool,
    LEM:bool,
    negNegE:bool,
    PBC:bool,
}

#[derive(Default)]
struct ProofGenSettings {
    disable_bot_generation:bool,
    disable_bot_in_context:bool, // unimplemented
    disable_free_variable_generation:bool,
}


impl IntoIterator for Rule {
    type Item = NodeID;

    type IntoIter = std::vec::IntoIter<NodeID>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Rule::Ax | Rule::LEM => {
                vec![]
            }
            Rule::AndE1(id)
            | Rule::AndE2(id)
            | Rule::ImpI(id)
            | Rule::OrI1(id)
            | Rule::OrI2(id)
            | Rule::BotE(id)
            | Rule::NegI(id)
            | Rule::NegNegI(id)
            | Rule::NegNegE(id)
            | Rule::PBC(id) => {
                vec![id]
            }
            Rule::AndI(id1, id2)
            | Rule::ImpE(id1, id2)
            | Rule::NegE(id1, id2)
            | Rule::MT(id1, id2) => {
                vec![id1, id2]
            }
            Rule::OrE(id1, id2, id3) => {
                vec![id1, id2, id3]
            }
        }
        .into_iter()
    }
}

fn main() {
    use Formula::*;
    let formula_to_prove = Sequent {
        context: BTreeSet::from_iter([-(Formula::Var(1) * Formula::Var(2))]),
        rest: -Formula::Var(1) + -Formula::Var(2),
        max_free_var: 2,
    };

    println!(
        "Truth_value: {}",
        formula_to_prove.valid_nk_via_truth_tables()
    );

    println!("eq is functioning: {:?}", (Var(1) >> Var(1)) == ((Var(1) >> Var(1))));
    let mut testeqmap = BTreeSet::new();
    testeqmap.insert(Var(1));
    println!("eq is functioning: {:?}", (Sequent{ context: testeqmap.clone(), rest: Var(1), max_free_var: 1 }) ==  Sequent{ context: testeqmap.clone(), rest: Var(1), max_free_var: 1 });
    let mut testbset = BTreeSet::new();
    testbset.insert(Sequent{ context: testeqmap.clone(), rest: Var(1), max_free_var: 1 });
    println!("{}", testbset.contains(&Sequent{ context: testeqmap.clone(), rest: Var(1), max_free_var: 1 }));


    let mut rmap = BTreeMap::new();
    let res: Vec<_> = Formula::gen_of_size(1, 5, &mut rmap, false, false)
        .into_iter()
        .map(|(a, _)| a)
        .collect();

    //println!("{:?}", res);

    let mut proof_tree = ProofSearchTree {
        nodes: vec![],
        sequents: BTreeMap::new(),
        banned_rules: BannedRules{PBC:true, negNegE:true, LEM:true, botE:true,  ..Default::default()},
        settings: ProofGenSettings { disable_bot_generation: true, disable_bot_in_context: true, disable_free_variable_generation: true }
        //banned_rules: BannedRules{PBC:true, negNegE:true, LEM:true, botE:true, ..Default::default()}
        //banned_rules: BannedRules { ax: false, andE1: false, andE2: false, andI: true, impI: false, impE: true, orI1: true, orI2: true, orE: true, botE: true, negE: true, negI: true, negNegI: true, MT: true, LEM: true, negNegE: true, PBC: true }
    };
    
    proof_tree.add_node(
        0,
        0,
        Sequent {
            context: BTreeSet::new(),
            //rest: (Var(1)) >> (--Var(1)),
            //rest: (Var(1) >> Var(2)) >> (-Var(2) >> -Var(1)),
            //rest: -(Var(1) + Var(2)) >> (-Var(1) * -Var(2)),
            //rest: (-Var(1) * -Var(2)) >> -(Var(1) + Var(2)),
            rest: (Var(1) * Var(2)) >> (Var(2) * Var(1)),
            //rest: (---Var(1)) >> (-Var(1)),
            //rest: (Var(1) * Var(2)) >> (Var(1) >> Var(2)),
            //rest: (Var(1) >> Bot) >> -Var(1),
            //rest: Var(1) >> (Var(2) >> (Var(1) * Var(2))),
            // rest: (Var(1) >> (Var(2) >> Var(3)) ) >> ((Var(1) >> Var(2)) >> (Var(1) >> Var(3))),
            max_free_var: 2,
        },
        0,
                    0,
    );
    
    // todo heuristics based on depth, gendepth, node size, DFSish
    // like for example find the smallest set of unproved formulas sufficient for a proof, bfs over each of those. 
    
    let mut depth = 0;
    while !proof_tree.nodes[0].is_proven() {
        //println!("depth = {}", depth);
        let mut prev_node_count = proof_tree.nodes.len();
        loop {
            let mut nodes = vec![];
            for node in &mut proof_tree.nodes {
                if node.is_unproved() {
                    nodes.push(node.id);
                }
            }
            for nodeid in nodes {
                proof_tree.extend_by_into(0,nodeid);
            }
            if proof_tree.nodes.len() == prev_node_count {
                break
            } else {
                prev_node_count = proof_tree.nodes.len()
            }   
        }
        println!("depth: {}", depth);
        //println!("Continue attempting proof?");
        //std::io::stdin().read_line(&mut "".to_string());

        
        if proof_tree.nodes[0].is_proven() {
            break
        }
        depth += 1;
        let mut nodes = vec![];
        for node in &mut proof_tree.nodes {
            if node.is_unproved() {
                nodes.push((node.id, node.gendepth));
            }
        }
        for (nodeid,nodedepth) in nodes {
            if depth as i32 - nodedepth as i32 > 0 {
                proof_tree.extend_by_into(depth - nodedepth,nodeid ); 
                if proof_tree.nodes[0].is_proven() {
                    break
                }

            }
        }

    }

    for line in proof_tree.get_proof(0){
        println!("{}",line);
    }


    /*

    for size in 1..
      for proof in unfinishedProofs:
        for newproof in proof.extendToLength(size - proof.size())
          if newproof.unfinishedRules.isEmpty():
            return newproof
          else if newproof.satisfiable():
            unfinishedProofs.add(newproof)
     */
}



/*

-------ax -------ax      
 A,B⊢A     A,B⊢A         
 ---------------∧i    
     A,B⊢A∧B       
    ---------⇒i  
     B⊢A⇒B∧A     
    ----------⇒i
     ⊢A⇒B⇒A∧B   

*/



/*
---A,A | A    ---A,A | -A
----------- -e
---A,A | T
----------- -i
---A | -A
-----------=>i
---A >> -A,

*/
