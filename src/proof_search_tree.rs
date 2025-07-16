
    use std::{cmp::max, collections::{BTreeMap, BTreeSet, HashMap}};

    use itertools::Itertools;

    use crate::{formula::Formula, sequent::Sequent, BannedRules, Node, NodeID, NodeState, ProofGenSettings, Rule, RuleID};


pub struct ProofSearchTree {
    pub nodes: Vec<Node>,
    pub sequents: HashMap<Sequent, NodeID>,
    pub banned_rules : BannedRules,
    pub settings : ProofGenSettings,
}

impl ProofSearchTree {
    fn next_node_id(&self) -> NodeID {
        self.nodes.len()
    }

    // DOES NOT MODIFY PARENT!!! caller needs to add rule and check if proven
    pub fn add_node(
        &mut self,
        parent: NodeID,
        rule: RuleID,
        data: Sequent,
        parent_gendepth: u32,
        parent_depth: u32,
    ) -> Option<NodeID> {
        let data_normal = data.alpha_eq_normal_form();
        //println!("add_node: {} | {}", data, data_normal);
        use NodeState::*;
        if let Some(&nodeID) = self.sequents.get(&data_normal) {
            //println!("add_node: node exists");
            let node = self.get_node(nodeID);
            match node.state {
                Redundant => node.state = RequiredBy(1),
                RequiredBy(n) => node.state = RequiredBy(n + 1),
                ProvenBy(_) => {}
            }
            Some(nodeID)
        } else if !data.valid_nk_via_truth_tables() {
            // These none values should probably also be in the btree uhh TODO?
            //println!("add_node: sequent false");
            None
        } else {
            //println!("add_node: adding");
            //println!("add_node: {:?}", self.sequents);
            self.nodes.push(Node {
                parents: vec![(parent, rule)],
                possible_subproofs: vec![],
                data: data_normal.clone(),
                state: NodeState::RequiredBy(1),
                id: self.next_node_id(), // risky
                gendepth: parent_gendepth,
                depth: parent_depth + 1,
                next_expansion: 0,
            });
            self.sequents.insert(data_normal, self.next_node_id() - 1);
            Some(self.next_node_id() - 1) // riskier
        }
        
    }

    pub fn mark_proved(&mut self, id: NodeID, by:RuleID) {
        if let NodeState::ProvenBy(_) = self.get_node(id).state {
            return;
        }
        println!("mark_proved: proof reached in node {}!", self.get_node(id).data);
        self.get_node(id).state = NodeState::ProvenBy(by);
        let parents: Vec<(NodeID, RuleID)> = self.get_node(id).parents.clone();
        for (pnodeid, rule) in parents {
            let pnode = self.get_node(pnodeid);
            let crule = pnode.possible_subproofs[rule];
            let all_siblings_proven = crule.into_iter().fold(true, |acc, b| {
                if let NodeState::ProvenBy(_) = self.get_node(b).state {acc} else {false}
            });
            if all_siblings_proven {
                self.mark_proved(pnodeid, rule);
                let cousins = self
                    .get_node(pnodeid)
                    .possible_subproofs
                    .clone()
                    .into_iter()
                    .flatten();
                for cousin in cousins {
                    self.mark_potentially_redundant(cousin);
                }
            }
        }
    }

    pub fn mark_potentially_redundant(&mut self, id: NodeID) {
        match self.get_node(id).state {
            NodeState::RequiredBy(1) => (),
            NodeState::RequiredBy(x) => {
                self.get_node(id).state = NodeState::RequiredBy(x - 1);
                return;
            }
            _ => return,
        };

        self.get_node(id).state = NodeState::Redundant;
        let children: Vec<NodeID> = self
            .get_node(id)
            .possible_subproofs
            .clone()
            .into_iter()
            .flatten()
            .unique()
            .collect();
        for child in children {
            self.mark_potentially_redundant(child);
        }
    }

    pub fn get_node(&mut self, id: NodeID) -> &mut Node {
        &mut self.nodes[id]
    }

fn center_pad(s: &str, w: usize) -> String {
    let len = Self::raw_len(s);
    if w <= len {
        return s.to_string();
    }
    let total_pad = w - len;
    let left = total_pad / 2;
    let right = total_pad - left;
    format!("{}{}{}", " ".repeat(left), s, " ".repeat(right))
}

/// Count chars excluding surrounding spaces
fn raw_len(s: &str) -> usize {
    s.chars().count()
}

fn gen_proof_rule0(btm: String, rulename: &str) -> Vec<String> {
    let width = Self::raw_len(&btm);
    let line = format!("{}{}", "-".repeat(width), rulename);
    vec![line, btm.to_string()+&" ".repeat(Self::raw_len(rulename))]
}

fn gen_proof_rule1(btm: String, rulename: &str, mut prev: Vec<String>) -> Vec<String> {
    let child_w = Self::raw_len(&prev[0]);
    let concl_w = Self::raw_len(&btm);
    let width = max(child_w, concl_w);
    let line = format!("{}{}", "-".repeat(width), rulename);
    prev.iter_mut().for_each(|f| *f = Self::center_pad(f, width) + &" ".repeat(Self::raw_len(rulename)));
    let btm = Self::center_pad(&btm, width) + &" ".repeat(Self::raw_len(rulename));
    let mut result = prev;
    result.push(line);
    result.push(btm);
    result
}

fn gen_proof_rule2( // todo bottom bigger than top case
    btm: String,
    rulename: &str,
    mut left: Vec<String>,
    mut right: Vec<String>,
) -> Vec<String> {
    let lw = Self::raw_len(&left[0]);
    let rw = Self::raw_len(&right[0]);
    let frac_children = lw + rw + 1;
    let concl_w = Self::raw_len(&btm);
    let width = max(frac_children, concl_w);
    // align heights by inserting blank lines at top
    let lh = left.len();
    let rh = right.len();
    if lh < rh {
        let blank = " ".repeat(lw);
        for _ in 0..(rh - lh) {
            left.insert(0, blank.clone());
        }
    } else if rh < lh {
        let blank = " ".repeat(rw);
        for _ in 0..(lh - rh) {
            right.insert(0, blank.clone());
        }
    }
    // merge and center to total width
    let mut merged: Vec<String> = left
        .into_iter()
        .zip(right.into_iter())
        .map(|(l, r)| l + " "+  &r + &" ".repeat(Self::raw_len(rulename)))
        .collect();
    let btm = Self::center_pad(&btm, width) + &" ".repeat(Self::raw_len(rulename));
    let line = format!("{}{}", "-".repeat(width), rulename);
    merged.push(line);
    merged.push(btm);
    merged
}

fn gen_proof_rule3(
    btm: String,
    rulename: &str,
    mut a: Vec<String>,
    mut b: Vec<String>,
    mut c: Vec<String>,
) -> Vec<String> {
    let aw = Self::raw_len(&a[0]);
    let bw = Self::raw_len(&b[0]);
    let cw = Self::raw_len(&c[0]);
    let frac_children = aw + bw + cw + 2;
    let concl_w = Self::raw_len(&btm);
    let width = max(frac_children, concl_w);
    // pad individual widths
    // align heights
    let h = *[a.len(), b.len(), c.len()].iter().max().unwrap();
    let blank_a = " ".repeat(aw);
    let blank_b = " ".repeat(bw);
    let blank_c = " ".repeat(cw);
    while a.len() < h { a.insert(0, blank_a.clone()); }
    while b.len() < h { b.insert(0, blank_b.clone()); }
    while c.len() < h { c.insert(0, blank_c.clone()); }
    // merge
    let mut merged: Vec<String> = (0..h)
        .map(|i| (a[i].clone() + " " + &b[i] + " " + &c[i] + &" ".repeat(Self::raw_len(rulename))))
        .collect();
    let btm = Self::center_pad(&btm, width) + &" ".repeat(Self::raw_len(rulename));
    let line = format!("{}{}", "-".repeat(width), rulename);
    merged.push(line);
    merged.push(btm);
    merged
}

    pub fn get_proof(&mut self, id:NodeID)->Vec<String> {
        let seq = self.get_node(id).data.to_string();
        if let NodeState::ProvenBy(rule) = self.get_node(id).state {
            match self.get_node(id).possible_subproofs[rule]{
                Rule::Ax => 
                    Self::gen_proof_rule0(seq, "ax"),
                Rule::AndE1(nid1) => 
                    Self::gen_proof_rule1(seq, "∧e1", self.get_proof(nid1)),
                Rule::AndE2(nid1) =>
                    Self::gen_proof_rule1(seq, "∧e2", self.get_proof(nid1)),
                Rule::AndI(nid1, nid2) => 
                    Self::gen_proof_rule2(seq, "∧i", self.get_proof(nid1), self.get_proof(nid2)),
                Rule::ImpI(nid1) => 
                    Self::gen_proof_rule1(seq, "⇒i", self.get_proof(nid1)),
                Rule::ImpE(nid1, nid2) => 
                    Self::gen_proof_rule2(seq, "⇒e", self.get_proof(nid1), self.get_proof(nid2)),
                Rule::OrI1(nid1) => 
                    Self::gen_proof_rule1(seq, "∨i1", self.get_proof(nid1)),
                Rule::OrI2(nid1) => 
                    Self::gen_proof_rule1(seq, "∨i2", self.get_proof(nid1)),
                Rule::OrE(nid1, nid2, nid3) => 
                    Self::gen_proof_rule3(seq, "∨e", self.get_proof(nid1), self.get_proof(nid2), self.get_proof(nid3)),
                Rule::BotE(nid1) => 
                    Self::gen_proof_rule1(seq, "⊥e", self.get_proof(nid1)),
                Rule::NegE(nid1, nid2) => 
                    Self::gen_proof_rule2(seq, "¬e", self.get_proof(nid1), self.get_proof(nid2)),
                Rule::NegI(nid1) => 
                    Self::gen_proof_rule1(seq, "¬i", self.get_proof(nid1)),
                Rule::NegNegI(nid1) => 
                    Self::gen_proof_rule1(seq, "¬¬i", self.get_proof(nid1)),
                Rule::MT(nid1, nid2) => 
                    Self::gen_proof_rule2(seq, "MT", self.get_proof(nid1), self.get_proof(nid2)),
                Rule::LEM => 
                    Self::gen_proof_rule0(seq, "LEM"),
                Rule::NegNegE(nid1) => 
                    Self::gen_proof_rule1(seq, "¬¬e", self.get_proof(nid1)),
                Rule::PBC(nid1) => 
                    Self::gen_proof_rule1(seq, "PBC", self.get_proof(nid1)),
            }
        } else {
            vec!["unproven".to_string()]
        }
    }

    pub fn extend_by_into(&mut self, amount: u32, innodeid:NodeID) -> bool {
        use Formula::*;
        if ! matches!(self.get_node(innodeid).state, NodeState::RequiredBy(_)){
            return false
        }
        let mut addedNodes = vec![];
        self.get_node(innodeid).next_expansion = max(amount + 1, self.get_node(innodeid).next_expansion);
        let innode = self.get_node(innodeid).clone();
        let mut newdepth =  innode.gendepth;
        if amount == 0 {
            if innode.data.context.contains(&innode.data.rest) && !self.banned_rules.ax {
                self.get_node(innodeid).possible_subproofs.push(Rule::Ax);
                let ruleid = self.get_node(innodeid).possible_subproofs.len()-1;
                self.mark_proved(innodeid, ruleid);
                return true;
            }
            if !self.banned_rules.PBC {
                let mut newctx = innode.data.context.clone();
                newctx.insert(-innode.data.rest.clone());
                let rulenum = self.get_node(innodeid).possible_subproofs.len();
                let new_node = self.add_node(
                    innodeid,
                    rulenum,
                    Sequent {   
                        context: newctx,
                        rest: Bot,
                        max_free_var: innode.data.max_free_var,
                    },
                    newdepth,
                    innode.depth,
                );
                if let Some(x) = new_node {
                    addedNodes.push(x);
                    self.get_node(innodeid).possible_subproofs.push(Rule::PBC(x));
                };
            }
            if !self.banned_rules.botE {
                let rulenum = self.get_node(innodeid).possible_subproofs.len();
                let new_node = self.add_node(
                    innodeid,
                    rulenum,
                    Sequent {
                        context: innode.data.context.clone(),
                        rest: Bot,
                        max_free_var: innode.data.max_free_var,
                    },
                    newdepth,
                    innode.depth,
                );
                if let Some(x) = new_node {
                    addedNodes.push(x);
                    self.get_node(innodeid).possible_subproofs.push(Rule::BotE(x));
                };
            }
            if !self.banned_rules.negNegE {
                let rulenum = self.get_node(innodeid).possible_subproofs.len();
                let new_node = self.add_node(
                    innodeid,
                    rulenum,
                    Sequent {
                        context: innode.data.context.clone(),
                        rest: --innode.data.rest.clone(),
                        max_free_var: innode.data.max_free_var,
                    },
                    newdepth,
                    innode.depth,
                );
                if let Some(x) = new_node {
                    addedNodes.push(x);
                    self.get_node(innodeid).possible_subproofs.push(Rule::NegNegE(x));
                };
            }

            match innode.data.rest.clone() {
                Neg(f1) => {
                    if !self.banned_rules.negI {
                        let mut newctx: BTreeSet<Formula> = innode.data.context.clone();
                        newctx.insert(*f1.clone());
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: newctx,
                                rest: Bot,
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        if let Some(x) = new_node {
                            addedNodes.push(x);
                            self.get_node(innodeid).possible_subproofs.push(Rule::NegI(x));
                        };
                    }
                    if !self.banned_rules.negNegI {
                        if let Neg(f1prime) = *f1.clone() {
                let rulenum = self.get_node(innodeid).possible_subproofs.len();
                            let new_node = self.add_node(
                                innodeid,
                                rulenum,
                                Sequent {
                                    context: innode.data.context.clone(),
                                    rest: *f1prime,
                                    max_free_var: innode.data.max_free_var,
                                },
                                newdepth,
                    innode.depth,
                            );
                            if let Some(x) = new_node {
                                addedNodes.push(x);
                                self.get_node(innodeid).possible_subproofs.push(Rule::NegNegI(x));
                            };
                        }
                    }
                }
                Formula::Imp(f1, f2) => {
                    if !self.banned_rules.impI {
                        let mut newctx: BTreeSet<Formula> = innode.data.context.clone();
                        newctx.insert(*f1);

                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: newctx,
                                rest: *f2,
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        if let Some(x) = new_node {
                            addedNodes.push(x);
                            self.get_node(innodeid).possible_subproofs.push(Rule::ImpI(x));
                        };
                    }
                }
                Formula::Or(f1, f2) => {
                    if !self.banned_rules.orI1 {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: innode.data.context.clone(),
                                rest: *f1.clone(),
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        if let Some(x) = new_node {
                            addedNodes.push(x);
                            self.get_node(innodeid).possible_subproofs.push(Rule::OrI1(x));
                        };
                    }
                    if !self.banned_rules.orI2 {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: innode.data.context.clone(),
                                rest: *f2.clone(),
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        if let Some(x) = new_node {
                            addedNodes.push(x);
                            self.get_node(innodeid).possible_subproofs.push(Rule::OrI2(x));
                        };
                    }
                    if *f2.clone() == -*f1.clone() && !self.banned_rules.LEM {
                        self.get_node(innodeid).possible_subproofs.push(Rule::LEM);
                        let ruleid = self.get_node(innodeid).possible_subproofs.len()-1;
                        self.mark_proved(innodeid, ruleid);
                        return true;
                    }
                }
                Formula::And(f1, f2) => {
                    if !self.banned_rules.andI {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node1 = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: innode.data.context.clone(),
                                rest: *f1,
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node2 = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: innode.data.context.clone(),
                                rest: *f2,
                                max_free_var: innode.data.max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        match (new_node1, new_node2) {
                            (None, None) => {}
                            (None, Some(x)) | (Some(x), None) => {
                                self.mark_potentially_redundant(x);
                            }
                            (Some(x1), Some(x2)) => {
                                addedNodes.push(x1);
                                addedNodes.push(x2);
                                self.get_node(innodeid).possible_subproofs.push(Rule::AndI(x1, x2));
                            }
                        }
                    }
                }
                _ => (),
            }
        } else {
            newdepth += 1;
            let mut map = BTreeMap::new();
            let formulae = Formula::gen_of_size(amount, innode.data.max_free_var, &mut map, self.settings.disable_bot_generation, self.settings.disable_free_variable_generation);
            for (genformula, max_free_var) in formulae {
                if !self.banned_rules.andE1 {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                    let new_node = self.add_node(
                        innodeid,
                        rulenum,
                        Sequent {
                            context: innode.data.context.clone(),
                            rest: innode.data.rest.clone() * genformula.clone(),
                            max_free_var,
                        },
                        newdepth,
                    innode.depth,
                    );
                    if let Some(x) = new_node {
                        addedNodes.push(x);
                        self.get_node(innodeid).possible_subproofs.push(Rule::AndE1(x));
                    };
                }
                if !self.banned_rules.andE2 {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                    let new_node = self.add_node(
                        innodeid,
                        rulenum,
                        Sequent {
                            context: innode.data.context.clone(),
                            rest: genformula.clone() * innode.data.rest.clone(),
                            max_free_var,
                        },
                        newdepth,
                    innode.depth,
                    );
                    if let Some(x) = new_node {
                        addedNodes.push(x);
                        self.get_node(innodeid).possible_subproofs.push(Rule::AndE2(x));
                    };
                }
                if !self.banned_rules.impE {
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                    let new_node1 = self.add_node(
                        innodeid,
                        rulenum,
                        Sequent {
                            context: innode.data.context.clone(),
                            rest: genformula.clone() >> innode.data.rest.clone(),
                            max_free_var,
                        },
                        newdepth,
                    innode.depth,
                    );
                    let rulenum = self.get_node(innodeid).possible_subproofs.len();
                    let new_node2 = self.add_node(
                        innodeid,
                        rulenum,
                        Sequent {
                            context: innode.data.context.clone(),
                            rest: genformula.clone(),
                            max_free_var,
                        },
                        newdepth,
                    innode.depth,
                    );
                    match (new_node1, new_node2) {
                        (None, None) => {}
                        (None, Some(x)) | (Some(x), None) => {
                            self.mark_potentially_redundant(x);
                        }
                        (Some(x1), Some(x2)) => {
                            addedNodes.push(x1);
                            addedNodes.push(x2);
                            self.get_node(innodeid).possible_subproofs.push(Rule::ImpE(x1, x2));
                        }
                    }
                }
                match innode.data.rest.clone() {
                    Bot => {
                        if !self.banned_rules.negE {
                            let rulenum = self.get_node(innodeid).possible_subproofs.len();
                            let new_node1 = self.add_node(
                                innodeid,
                                rulenum,
                                Sequent {
                                    context: innode.data.context.clone(),
                                    rest: genformula.clone(),
                                    max_free_var,
                                },
                                newdepth,
                    innode.depth,
                            );
                            let rulenum = self.get_node(innodeid).possible_subproofs.len();
                            let new_node2 = self.add_node(
                                innodeid,
                                rulenum,
                                Sequent {
                                    context: innode.data.context.clone(),
                                    rest: -genformula.clone(),
                                    max_free_var,
                                },
                                newdepth,
                    innode.depth,
                            );
                            match (new_node1, new_node2) {
                                (None, None) => {}
                                (None, Some(x)) | (Some(x), None) => {
                                    self.mark_potentially_redundant(x);
                                }
                                (Some(x1), Some(x2)) => {
                                    addedNodes.push(x1);
                                    addedNodes.push(x2);
                                    self.get_node(innodeid).possible_subproofs.push(Rule::NegE(x1, x2));
                                }
                            }
                        }
                    }
                    Neg(f1) => {
                        if !self.banned_rules.MT {
                            let rulenum = self.get_node(innodeid).possible_subproofs.len();
                            let new_node1 = self.add_node(
                                innodeid,
                                rulenum,
                                Sequent {
                                    context: innode.data.context.clone(),
                                    rest: *f1 >> genformula.clone(),
                                    max_free_var,
                                },
                                newdepth,
                    innode.depth,
                            );
                            let rulenum = self.get_node(innodeid).possible_subproofs.len();
                            let new_node2 = self.add_node(
                                innodeid,
                                rulenum,
                                Sequent {
                                    context: innode.data.context.clone(),
                                    rest: -genformula.clone(),
                                    max_free_var,
                                },
                                newdepth,
                    innode.depth,
                            );
                            match (new_node1, new_node2) {
                                (None, None) => {}
                                (None, Some(x)) | (Some(x), None) => {
                                    self.mark_potentially_redundant(x);
                                }
                                (Some(x1), Some(x2)) => {
                                    addedNodes.push(x1);
                                    addedNodes.push(x2);
                                    self.get_node(innodeid).possible_subproofs.push(Rule::MT(x1, x2));
                                }
                            }
                        }
                    }
                    _ => {}
                }
                if !self.banned_rules.orE {if let Or(f1, f2) = genformula {
                    let mut context1 = innode.data.context.clone();
                    let mut context2 = context1.clone();
                    context1.insert(*f1.clone());
                    context2.insert(*f2.clone());
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node1 = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: innode.data.context.clone(),
                                rest: *f1 + *f2,
                                max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node2 = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: context1,
                                rest: innode.data.rest.clone(),
                                max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );
                        let rulenum = self.get_node(innodeid).possible_subproofs.len();
                        let new_node3 = self.add_node(
                            innodeid,
                            rulenum,
                            Sequent {
                                context: context2,
                                rest: innode.data.rest.clone(),
                                max_free_var,
                            },
                            newdepth,
                    innode.depth,
                        );

                        match (new_node1, new_node2, new_node3) {
                            (None, None, None) => {}
                            (None, Some(x), None)
                            | (Some(x), None, None)
                            | (None, None, Some(x)) => {
                                self.mark_potentially_redundant(x);
                            }
                            (None, Some(x1), Some(x2))
                            | (Some(x1), None, Some(x2))
                            | (Some(x1), Some(x2), None) => {
                                self.mark_potentially_redundant(x1);
                                self.mark_potentially_redundant(x2);
                            }
                            (Some(x1), Some(x2), Some(x3)) => {
                                addedNodes.push(x1);
                                addedNodes.push(x2);
                                self.get_node(innodeid).possible_subproofs.push(Rule::OrE(x1, x2, x3));
                            }
                        }
                }}
            }
        }

        false
    }
}