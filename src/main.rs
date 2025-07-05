use std::{collections::{BTreeMap, BTreeSet, HashSet}, iter::Product, ops::{Add, Deref, Index, Mul, Neg, Shr}};
use formula::Formula;
mod formula; // WHAT????
use itertools::Itertools;

type NodeID = usize;
type RuleID = usize;



//type Clausule = BTreeSet<Formula>;
//type ClausuleSet = BTreeSet<Clausule>;

struct ProofSearchTree {
    nodes: Vec<Node>,
    sequents:BTreeMap<Sequent, NodeID>,
}

impl ProofSearchTree {
    fn next_node_id(&self)->NodeID {
        self.nodes.len()
    }

    // DOES NOT MODIFY PARENT!!! caller needs to add rule and check if proven
    fn add_node(&mut self, parent:NodeID, rule:RuleID, data:Sequent, parent_depth:u32)->Option<NodeID>{
        let data_normal = data.alpha_eq_normal_form();
        use NodeState::*;
        if let Some(&nodeID) = self.sequents.get(&data_normal) {
            let node = self.get_node(nodeID);
            match node.state {
                Redundant => {node.state = RequiredBy(1)},
                RequiredBy(n) => {node.state = RequiredBy(n+1)},
                Proven => {}, 
            }
        } else if !data.valid_nk_via_truth_tables() { // These none values should probably also be in the btree uhh TODO?
            return None;
        } else {
            self.nodes.push(Node{
                parents: vec![(parent,rule)], 
                possible_subproofs: vec![],
                data: data_normal,
                state : NodeState::RequiredBy(1),
                id:self.next_node_id(), // risky
                depth: parent_depth+1,
            });
        }
        Some(self.next_node_id() - 1) // riskier
    }

    fn mark_proved(&mut self, id:NodeID) {
        if self.get_node(id).state == NodeState::Proven  {
            return;
        }
        self.get_node(id).state = NodeState::Proven;
        let parents:Vec<(NodeID,RuleID)> = self.get_node(id).parents.clone();
        for (pnodeid, rule) in parents {
            let pnode = self.get_node(pnodeid);
            let crule = pnode.possible_subproofs[rule];
            let all_siblings_proven = crule.into_iter().fold(true, |acc,b| self.get_node(b).state == NodeState::Proven && acc);
            if all_siblings_proven {
                self.mark_proved(pnodeid);
                let cousins = self.get_node(pnodeid).possible_subproofs
                    .clone().into_iter().flatten();
                for cousin in cousins {
                    self.mark_potentially_redundant(cousin);
                }
            }
        }
    }

    fn mark_potentially_redundant(&mut self, id:NodeID) {
        match self.get_node(id).state {
            NodeState::RequiredBy(1) => (),
            NodeState::RequiredBy(x) => {self.get_node(id).state = NodeState::RequiredBy(x-1); return},
            _ => return
        };
            
        self.get_node(id).state = NodeState::Redundant;
        let children:Vec<NodeID> = self.get_node(id).possible_subproofs.clone().into_iter().flatten().unique().collect(); 
        for child in children { 
            self.mark_potentially_redundant(child);
        }
    }

    fn get_node(&mut self, id:NodeID) -> &mut Node {
        &mut self.nodes[id]
    }
}

struct Node {
    id:NodeID,
    parents: Vec<(NodeID, RuleID)>,
    possible_subproofs:Vec<Rule>, //children
    data:Sequent,
    state: NodeState,
    depth:u32
    // instead of tracking how many branches depend on the proof we can recursively check parents. itll be easier
}

#[derive(PartialEq,Eq)]
enum NodeState {
    Redundant, Proven, RequiredBy(u32)
}



impl Node {
    fn extend_by_into(&mut self, amount:u32, into:&mut ProofSearchTree)->bool{
        use Formula::*;
        let mut addedNodes = vec![];
        if amount == 0 {
            if self.data.context.contains(&self.data.rest) {
                self.possible_subproofs.push(Rule::Ax);
                into.mark_proved(self.id);
                return true
            }
            if true {
                let mut newctx = self.data.context.clone();
                newctx.insert(-self.data.rest.clone());
                let new_node = into.add_node(
                    self.id, 
                    self.possible_subproofs.len(), 
                    Sequent { context: newctx, rest: Bot, max_free_var: self.data.max_free_var},
                self.depth);       
                if let Some(x) = new_node{
                    addedNodes.push(x);
                    self.possible_subproofs.push(Rule::PBC(x));
                };
            }
            if true {
                let new_node = into.add_node(
                    self.id, 
                    self.possible_subproofs.len(), 
                    Sequent { context: self.data.context.clone(), rest: Bot, max_free_var: self.data.max_free_var },
                self.depth);       
                if let Some(x) = new_node{
                    addedNodes.push(x);
                    self.possible_subproofs.push(Rule::BotE(x));
                };
            }
            if true {
                let new_node = into.add_node(
                self.id, 
                self.possible_subproofs.len(), 
                Sequent { context: self.data.context.clone(), rest: --self.data.rest.clone() , max_free_var: self.data.max_free_var},
                self.depth);       
                if let Some(x) = new_node{
                    addedNodes.push(x);
                    self.possible_subproofs.push(Rule::NegNegE(x));
                };
            }
            
            match self.data.rest.clone() {
                Neg(f1) => {
                    if true {
                        let mut newctx: BTreeSet<Formula> = self.data.context.clone();
                        newctx.insert(*f1.clone());
                        let new_node = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: newctx, rest: Bot, max_free_var: self.data.max_free_var },
                self.depth);       
                        if let Some(x) = new_node{
                            addedNodes.push(x);
                            self.possible_subproofs.push(Rule::NegI(x));
                        };      
                    }
                    if true  {
                        if let Neg(f1prime) = *f1.clone() {
                            let new_node = into.add_node(
                                self.id,
                                self.possible_subproofs.len(),
                                Sequent { context: self.data.context.clone(), rest: *f1prime , max_free_var: self.data.max_free_var},
                self.depth);
                            if let Some(x) = new_node{
                                addedNodes.push(x);
                                self.possible_subproofs.push(Rule::NegNegI(x));
                            };
                        }
                    }
                },
                Formula::Imp(f1, f2) => {
                    if true {
                        let mut newctx: BTreeSet<Formula> = self.data.context.clone();
                        newctx.insert(*f1);     

                        let new_node = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest: *f2 , max_free_var: self.data.max_free_var},
                self.depth);       
                        if let Some(x) = new_node{
                            addedNodes.push(x);
                            self.possible_subproofs.push(Rule::ImpI(x));
                        };
 
                    }
                },
                Formula::Or(f1, f2) => {
                    if true {
                        let new_node = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest: *f1.clone() , max_free_var: self.data.max_free_var},
                self.depth);       
                        if let Some(x) = new_node{
                            addedNodes.push(x);
                            self.possible_subproofs.push(Rule::OrI1(x));
                        };
                    }
                    if true {
                        let new_node = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest: *f2.clone() , max_free_var: self.data.max_free_var},
                self.depth);       
                        if let Some(x) = new_node{
                            addedNodes.push(x);
                            self.possible_subproofs.push(Rule::OrI2(x));
                        };
                    }
                    if *f2.clone() == -*f1.clone()   {
                        self.possible_subproofs.push(Rule::LEM);
                        into.mark_proved(self.id);
                        return true
                    }
                },
                Formula::And(f1, f2) => {
                    if true {
                        let new_node1 = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest: *f1 , max_free_var: self.data.max_free_var},
                self.depth);
                        let new_node2 = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest: *f2 , max_free_var: self.data.max_free_var},
                self.depth);
                        match (new_node1, new_node2) {
                            (None, None) => {},
                            (None, Some(x)) | (Some(x), None) => {
                                into.mark_potentially_redundant(x);
                            },
                            (Some(x1), Some(x2)) => {
                                addedNodes.push(x1);
                                addedNodes.push(x2);
                                self.possible_subproofs.push(Rule::AndI(x1,x2));
                            },
                        }
                    }
                },
                _ => ()
            }
        } else {
            let mut map = BTreeMap::new();
            let formulae = Formula::gen_of_size(amount,self.data.max_free_var, &mut map, false);
            for (genformula,max_free_var) in formulae {
                if true {
                    let new_node = into.add_node(
                        self.id, 
                        self.possible_subproofs.len(), 
                        Sequent { context: self.data.context.clone(), rest: self.data.rest.clone() * genformula.clone() ,  max_free_var},
                self.depth);       
                    if let Some(x) = new_node{
                        addedNodes.push(x);
                        self.possible_subproofs.push(Rule::AndE1(x));
                    };
                }
                if true {
                    let new_node = into.add_node(
                        self.id, 
                        self.possible_subproofs.len(), 
                        Sequent { context: self.data.context.clone(), rest: genformula.clone() * self.data.rest.clone() , max_free_var},
                self.depth);       
                    if let Some(x) = new_node{
                        addedNodes.push(x);
                        self.possible_subproofs.push(Rule::AndE2(x));
                    };
                }
                if true {
                    let new_node1 = into.add_node(
                        self.id, 
                        self.possible_subproofs.len(), 
                        Sequent { context: self.data.context.clone(), rest:  genformula.clone() >> self.data.rest.clone() , max_free_var},
                self.depth);
                    let new_node2 = into.add_node(
                        self.id, 
                        self.possible_subproofs.len(), 
                        Sequent { context: self.data.context.clone(), rest: genformula.clone() , max_free_var},
                self.depth);
                    match (new_node1, new_node2) {
                        (None, None) => {},
                        (None, Some(x)) | (Some(x), None) => {
                            into.mark_potentially_redundant(x);
                        },
                        (Some(x1), Some(x2)) => {
                            addedNodes.push(x1);
                            addedNodes.push(x2);
                            self.possible_subproofs.push(Rule::ImpE(x1,x2));
                        },
                    }

                }
                match self.data.rest.clone() {
                    Bot => {
                        if true {
                            let new_node1 = into.add_node(
                                self.id, 
                                self.possible_subproofs.len(), 
                                Sequent { context: self.data.context.clone(), rest:  genformula.clone() , max_free_var},
                self.depth);
                            let new_node2 = into.add_node(
                                self.id, 
                                self.possible_subproofs.len(), 
                                Sequent { context: self.data.context.clone(), rest: -genformula.clone() , max_free_var},
                self.depth);
                            match (new_node1, new_node2) {
                                (None, None) => {},
                                (None, Some(x)) | (Some(x), None) => {
                                    into.mark_potentially_redundant(x);
                                },
                                (Some(x1), Some(x2)) => {
                                    addedNodes.push(x1);
                                    addedNodes.push(x2);
                                    self.possible_subproofs.push(Rule::NegE(x1,x2));
                                },
                            }
                        }
                    },
                    Neg(f1) => {
                        if true {
                            let new_node1 = into.add_node(
                                self.id, 
                                self.possible_subproofs.len(), 
                                Sequent { context: self.data.context.clone(), rest:  *f1 >> genformula.clone() , max_free_var},
                self.depth);
                            let new_node2 = into.add_node(
                                self.id, 
                                self.possible_subproofs.len(), 
                                Sequent { context: self.data.context.clone(), rest: -genformula.clone() , max_free_var},
                self.depth);
                            match (new_node1, new_node2) {
                                (None, None) => {},
                                (None, Some(x)) | (Some(x), None) => {
                                    into.mark_potentially_redundant(x);
                                },
                                (Some(x1), Some(x2)) => {
                                    addedNodes.push(x1);
                                    addedNodes.push(x2);
                                    self.possible_subproofs.push(Rule::MT(x1,x2));
                                },
                            }
                        }
                    },
                    _ => {}
                }
                if let Or(f1,f2) = genformula {
                    let mut context1 = self.data.context.clone();
                    let mut context2 = context1.clone();
                    context1.insert(*f1.clone());
                    context2.insert(*f2.clone());
                    if true {
                        let new_node1 = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: self.data.context.clone(), rest:  *f1 + *f2 , max_free_var},
                self.depth);
                        let new_node2 = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: context1, rest:self.data.rest.clone() , max_free_var},
                self.depth);
                        let new_node3 = into.add_node(
                            self.id, 
                            self.possible_subproofs.len(), 
                            Sequent { context: context2, rest:self.data.rest.clone() , max_free_var},
                self.depth);

                        match (new_node1, new_node2, new_node3) {
                            (None, None, None) => {},
                            (None, Some(x), None) | (Some(x), None, None) | (None, None, Some(x)) => {
                                into.mark_potentially_redundant(x);
                            },
                            (None, Some(x1), Some(x2)) | (Some(x1), None, Some(x2)) | (Some(x1), Some(x2), None) => {
                                into.mark_potentially_redundant(x1);
                                into.mark_potentially_redundant(x2);
                            },
                            (Some(x1), Some(x2), Some(x3)) => {
                                addedNodes.push(x1);
                                addedNodes.push(x2);
                                self.possible_subproofs.push(Rule::OrE(x1,x2,x3));
                            },
                        }
                    }
                }
                

            }
        }
        

        false
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct Sequent {
    context:BTreeSet<Formula>,
    rest:Formula,
    max_free_var:u32
}

impl Sequent {
    fn valid_nk_via_truth_tables(&self) -> bool { // todo DPLL maybe?
        let mut free_vars = vec![];
        for formula in self.context.iter().chain(vec![&self.rest].into_iter()) {
            formula.fold((), &mut |v|free_vars.push(v), &|_|(), &|_,_|(), &|_,_|(), &|_,_|())
        } // probably not good
        free_vars = free_vars.into_iter().unique().collect();
        let mut valid_combinations:Vec<u32> = vec![];
        for truth_bits in 0.. 2_u32.pow(free_vars.len() as u32) {
            let mut is_valid = true;
            for formula in self.context.iter(){
                // suponemos que no puede haber bottom en el contexto porque no se que hacer 
                // son deducibles las reglas de => en ND?
                // existe una version "resumida" para LP como lo hay para LPO? de resolución
                // existe algo como debrujin index / 11para LP? 
                is_valid = is_valid && formula.fold(false, &mut |v|{
                    (2_u32.pow(free_vars.iter().position(|&x|x == v).unwrap() as u32) & truth_bits) != 0
                }, &|v| !v, &|v,w| !v || w, &|v: bool,w| v && w, &|v,w| v || w); 
            }
            if is_valid {
                valid_combinations.push(truth_bits);
            }
        } 

        let mut formula_is_valid = true;
        for truth_bits in valid_combinations {
            formula_is_valid = formula_is_valid && self.rest.fold(false, &mut |v|{
                    (2_u32.pow(free_vars.iter().position(|&x|x == v).unwrap() as u32) & truth_bits) != 0
                }, &|v| !v, &|v,w| !v || w, &|v: bool,w| v && w, &|v,w| v || w);
        }
        formula_is_valid
    }

    fn valid_nk_via_resolution(&self) -> bool {
        let mut base_formula = self.rest.clone(); 
        for item in self.context.iter() {
            base_formula = Formula::Or(Box::new(Formula::Neg(Box::new(item.clone()))), Box::new(base_formula));
        }
        /*base_formula = base_formula.fold(
            Formula::Bot, 
            &mut |x|Formula::Var(x), 
            &|x|Formula::Neg(Box::new(x)), 
            &|x,y|Formula::Or(Box::new(Formula::Neg(Box::new(x))),Box::new(y)), 
            &|x,y|Formula::And(Box::new(x),Box::new(y)), 
            &|x,y|Formula::Or(Box::new(x),Box::new(y)));  */ // yeah so fold was a really bad idea here
        todo!()
    }

    

    fn alpha_eq_normal_form(&self)->Self { // this should work, theres no bound variables. mybe look for counterexample??
        let mut free_vars = BTreeMap::new();
        let mut max_free_var = 0;
        let newres = self.rest.alpha_eq_normal_form(&mut free_vars,&mut max_free_var);
        Sequent {
             context: self.context.iter().map(|f|f.alpha_eq_normal_form(&mut free_vars, &mut max_free_var)).collect(), 
             rest: newres,
             max_free_var
            }
    }
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

impl IntoIterator for Rule {
    type Item = NodeID;

    type IntoIter = std::vec::IntoIter<NodeID>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
                Rule::Ax | Rule::LEM => {vec![]},
                Rule::AndE1(id) 
                | Rule::AndE2(id)   | Rule::ImpI(id)    | Rule::OrI1(id) 
                | Rule::OrI2(id)    | Rule::BotE(id)    | Rule::NegI(id) 
                | Rule::NegNegI(id) | Rule::NegNegE(id) | Rule::PBC(id) 
                    => {vec![id]},
                Rule::AndI(id1, id2)   | Rule::ImpE(id1, id2)
                | Rule::NegE(id1, id2) | Rule::MT(id1, id2) 
                    => {vec![id1,id2]}
                Rule::OrE(id1,id2 ,id3) =>
                    {vec![id1,id2,id3]}
        }.into_iter()
    }
}

fn main() {
    use Formula::*;
    let formula_to_prove = Sequent{
        context:BTreeSet::from_iter([-(Formula::Var(1) * Formula::Var(2))]), 
        rest: -Formula::Var(1) + -Formula::Var(2),
        max_free_var: 2
    };

    println!("Truth_value: {}", formula_to_prove.valid_nk_via_truth_tables());

    let mut rmap = BTreeMap::new();
    let res :Vec<_> = Formula::gen_of_size(1, 5, &mut rmap, false).into_iter().map(|(a,_)|a).collect();

    //println!("{:?}", res);
    
    let mut proof_tree = ProofSearchTree{ nodes: vec![], sequents: BTreeMap::new() };
    proof_tree.add_node(0, 0, Sequent { context: BTreeSet::new(), rest: Var(1) >> Var(1), max_free_var: 1 }, 0); 
    loop {

        for node in &mut proof_tree.nodes {
            //node.extend_by_into(1, &mut proof_tree);
        }
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
