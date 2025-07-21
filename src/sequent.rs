use std::collections::{BTreeMap, BTreeSet};

use itertools::Itertools;

use crate::formula::Formula;


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Sequent {
    pub context: BTreeSet<Formula>,
    pub rest: Formula,
    pub max_free_var: u32,
}

impl Sequent {
    pub fn valid_nk_via_truth_tables(&self) -> bool {
        // todo DPLL maybe?
        let mut free_vars = vec![];
        for formula in self.context.iter().chain(vec![&self.rest].into_iter()) {
            free_vars.extend(formula.get_free_vars().into_iter());
        } // probably not good
        free_vars = free_vars.into_iter().unique().collect();
        let mut valid_combinations: Vec<u32> = vec![];
        for truth_bits in 0..2_u32.pow(free_vars.len() as u32) {
            let mut is_valid = true;
            for formula in self.context.iter() {
                // suponemos que no puede haber bottom en el contexto porque no se que hacer
                // son deducibles las reglas de => en ND?
                // existe una version "resumida" para LP como lo hay para LPO? de resolución
                // existe algo como debrujin index / 11para LP?
                is_valid = is_valid
                    && formula.fold(
                        false,
                        &mut |v| {
                            (2_u32.pow(free_vars.iter().position(|&x| x == v).unwrap() as u32)
                                & truth_bits)
                                != 0
                        },
                        &|v| !v,
                        &|v, w| !v || w,
                        &|v: bool, w| v && w,
                        &|v, w| v || w,
                    );
            }
            if is_valid {
                valid_combinations.push(truth_bits);
            }
        }

        let mut formula_is_valid = true;
        for truth_bits in valid_combinations {
            formula_is_valid = formula_is_valid
                && self.rest.fold(
                    false,
                    &mut |v| {
                        (2_u32.pow(free_vars.iter().position(|&x| x == v).unwrap() as u32)
                            & truth_bits)
                            != 0
                    },
                    &|v| !v,
                    &|v, w| !v || w,
                    &|v: bool, w| v && w,
                    &|v, w| v || w,
                );
        }
        formula_is_valid
    }

    fn valid_nk_via_resolution(&self) -> bool {
        let mut base_formula = self.rest.clone();
        for item in self.context.iter() {
            base_formula = Formula::Or(
                Box::new(Formula::Neg(Box::new(item.clone()))),
                Box::new(base_formula),
            );
        }
        /*base_formula = base_formula.fold(
        Formula::Bot,
        &mut |x|Formula::Var(x),
        &|x|Formula::Neg(Box::new(x)),
        &|x,y|Formula::Or(Box::new(Formula::Neg(Box::new(x))),Box::new(y)),
        &|x,y|Formula::And(Box::new(x),Box::new(y)),
        &|x,y|Formula::Or(Box::new(x),Box::new(y)));  */
 // yeah so fold was a really bad idea here
        todo!()
    }

    pub fn alpha_eq_normal_form(self) -> Self { 
        // this should work, theres no bound variables. mybe look for counterexample??
        let mut free_vars = BTreeMap::new();
        let mut max_free_var = 0;
        let newres = self
            .rest
            .alpha_eq_normal_form(&mut free_vars, &mut max_free_var);
        Sequent {
            context: self
                .context
                .into_iter()
                .map(|f| f.alpha_eq_normal_form(&mut free_vars, &mut max_free_var))
                .collect(),
            rest: newres,
            max_free_var,
        }
    }
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}⊢{}", self.context.iter().join(","), self.rest)
    }
}

impl std::fmt::Debug for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}


/* 
impl std::ops::BitOr for Sequent {
    type Output = Sequent;
    type Rhs = Vec<Formula>;

    fn bitor(self, rhs: Self) -> Self::Output {
        todo!()
    }
}*/
