use core::panic;
use std::{
    cmp::Ordering,
    collections::BTreeMap,
    fmt::write,
    ops::{Add, Deref, Mul, Neg, Shr},
};


#[derive(Clone)]
pub enum Formula {
    Bot,
    Neg(Box<Self>),
    Imp(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Var(u32),
}

const VAR_INIT_NAME: u32 = 1;

fn var_to_char(i: u32) -> char {
    let mut i = i;
    i += 64;
    loop {
        if let Some(res) = char::from_u32(i) {
            return res;
        }
        i += 1;
    }
}

impl Formula {
    pub fn fold<T: Copy>(
        &self,
        bot: T,
        var: &mut dyn FnMut(u32) -> T,
        neg: &dyn Fn(T) -> T,
        imp: &dyn Fn(T, T) -> T,
        and: &dyn Fn(T, T) -> T,
        or: &dyn Fn(T, T) -> T,
    ) -> T {
        match self {
            Self::Bot => bot,
            Self::Var(i) => var(*i),
            Self::Neg(bx) => neg(bx.fold(bot, var, neg, imp, and, or)),
            Self::Imp(bx1, bx2) => imp(
                bx1.fold(bot, var, neg, imp, and, or),
                bx2.fold(bot, var, neg, imp, and, or),
            ),
            Self::And(bx1, bx2) => and(
                bx1.fold(bot, var, neg, imp, and, or),
                bx2.fold(bot, var, neg, imp, and, or),
            ),
            Self::Or(bx1, bx2) => or(
                bx1.fold(bot, var, neg, imp, and, or),
                bx2.fold(bot, var, neg, imp, and, or),
            ),
        }
    }

    pub fn alpha_eq_normal_form(
        &self,
        free_vars: &mut BTreeMap<u32, u32>,
        max_free_var: &mut u32,
    ) -> Formula {
        match self {
            Formula::Bot => Formula::Bot,
            Formula::Var(v) => {
                let newv = free_vars.entry(*v).or_insert_with(|| {
                    *max_free_var += 1;
                    *max_free_var
                });
                Formula::Var(*newv)
            }
            Formula::Neg(formula) => -(formula.alpha_eq_normal_form(free_vars, max_free_var)),
            Formula::Imp(f1, f2) => {
                f1.alpha_eq_normal_form(free_vars, max_free_var)
                    >> f2.alpha_eq_normal_form(free_vars, max_free_var)
            }
            Formula::And(f1, f2) => {
                f1.alpha_eq_normal_form(free_vars, max_free_var)
                    * f2.alpha_eq_normal_form(free_vars, max_free_var)
            }
            Formula::Or(f1, f2) => {
                f1.alpha_eq_normal_form(free_vars, max_free_var)
                    + f2.alpha_eq_normal_form(free_vars, max_free_var)
            }
        }
    }

    //TODO swap vec as parameter for iters
    pub fn gen_of_size(
        size: u32,
        max_free_var: u32,
        gen_of_size_map: &mut BTreeMap<(u32, u32), Vec<(Formula, u32)>>,
        disable_bot: bool,
    ) -> Vec<(Formula, u32)> {
        if let Some(res) = gen_of_size_map.get(&(size, max_free_var)) {
            return res.clone();
        }

        let mut res = vec![];
        if size == 1 {
            if disable_bot {
            } else {
                res.push((Formula::Bot, max_free_var))
            }; //todo with std::mem::discriminant so i can pass list to ignore
            for i in 1..=max_free_var {
                res.push((Formula::Var(i), max_free_var));
            }
            res.push((Formula::Var(max_free_var + 1), max_free_var + 1))
        } else {
            res.extend(
                Formula::gen_of_size(size - 1, max_free_var, gen_of_size_map, disable_bot)
                    .into_iter()
                    .map(|(a, b)| (-a, b)),
            );

            for i in 1..size {
                let left_formulae =
                    Formula::gen_of_size(i, max_free_var, gen_of_size_map, disable_bot);
                for (l_formula, max_free_var) in left_formulae.into_iter() {
                    let right_formulae =
                        Formula::gen_of_size(size - i, max_free_var, gen_of_size_map, disable_bot);
                    for (r_formula, max_free_var) in right_formulae {
                        res.push((l_formula.clone() + r_formula.clone(), max_free_var));
                        res.push((l_formula.clone() * r_formula.clone(), max_free_var));
                        res.push((l_formula.clone() >> r_formula.clone(), max_free_var));
                    }
                }
            }
        }
        gen_of_size_map.insert((size, max_free_var), res.clone());
        res
    }

    fn eliminate_implications(self) -> Formula {
        // dont remember if this one was functioning, i think it was
        match self {
            Formula::Bot => self,
            Formula::Var(_) => self,
            Formula::Neg(formula) => Formula::Neg(Box::new(formula.eliminate_implications())), // cant map box?
            Formula::Imp(f1, f2) => Formula::Or(
                Box::new(Formula::Neg(Box::new(f1.eliminate_implications()))),
                Box::new(f2.eliminate_implications()),
            ),
            Formula::And(f1, f2) => Formula::And(
                Box::new(f1.eliminate_implications()),
                Box::new(f2.eliminate_implications()),
            ),
            Formula::Or(f1, f2) => Formula::Or(
                Box::new(f1.eliminate_implications()),
                Box::new(f2.eliminate_implications()),
            ),
        }
    }

    fn push_neg(self) -> Formula {
        match self {
            Formula::Bot => self,
            Formula::Var(_) => self,
            Formula::Neg(formula) => match *formula {
                Formula::Bot => Formula::Neg(Box::new(Formula::Bot)),
                Formula::Var(v) => Formula::Neg(Box::new(Formula::Var(v))),
                Formula::Neg(fdouble_neg) => *fdouble_neg,
                Formula::And(f1, f2) => Formula::Or(
                    Box::new(Formula::Neg(Box::new(*f1)).push_neg()),
                    Box::new(Formula::Neg(Box::new(*f2)).push_neg()),
                ),
                Formula::Or(f1, f2) => Formula::And(
                    Box::new(Formula::Neg(Box::new(*f1)).push_neg()),
                    Box::new(Formula::Neg(Box::new(*f2)).push_neg()),
                ),
                _ => panic!("Invalid no imp formula"),
            },
            Formula::And(f1, f2) => Formula::And(Box::new(f1.push_neg()), Box::new(f2.push_neg())),
            Formula::Or(f1, f2) => Formula::Or(Box::new(f1.push_neg()), Box::new(f2.push_neg())),
            _ => panic!("Invalid no imp formula"),
        }
    }

    fn dist_ors(self) -> Formula {
        //todo tipos para NNF, terminar que esta todo medio mal
        match self {
            Formula::Bot => self,
            Formula::Var(_) => self,
            Formula::Neg(_) => self,
            Formula::And(f1, f2) => Formula::And(Box::new(f1.dist_ors()), Box::new(f2.dist_ors())),
            Formula::Or(f1, f2) => match *f1 {
                Formula::Bot => todo!(),
                Formula::Var(_) => todo!(),
                Formula::Neg(formula) => todo!(),
                Formula::And(formula, formula1) => todo!(),
                Formula::Or(formula, formula1) => todo!(),
                _ => panic!("Invalid no imp formula"),
            },
            _ => panic!("Invalid no imp formula"),
        }
    }

    fn rule_lower_prio(a: &Formula, b: &Formula) -> bool {
        match (a, b) {
            (_, Formula::Var(_)) => false,
            (_, Formula::Bot) => false,
            (_, Formula::Neg(_)) => false,
            (Formula::Neg(_), _) => true,
            (Formula::Imp(c, _), Formula::Imp(_, _)) => std::ptr::eq(c.as_ref(), b),
            (Formula::Imp(_, _), _) => false,
            (Formula::And(_, _), _) => true,
            (Formula::Or(_, _), _) => true,
            _ => panic!("invalid first rule"),
        }
    }
    fn to_string_parenth(&self, parent: &Formula) -> String {
        if Formula::rule_lower_prio(parent, self) {
            format!("({})", self.to_string())
        } else {
            format!("{}", self.to_string())
        }
    }
    //TODO make unpub
    pub fn cmp_structure(&self, other: &Self) -> std::cmp::Ordering {
        // unfortunate it has to be done this way. maybe reimplement if RFC3607 merged
        // sorts by structure first. doesnt matter how. if equal, then sorts by vars.
        use core::cmp::Ordering::*;
        use Formula::*;
        match self {
            Bot => match other {
                Bot => Equal,
                _ => Greater
            },
            Var(_) => match other {
                Bot => Less,
                Var(_) => Equal,
                _ => Greater,
            },
            Neg(formula) => match other {
                Bot | Var(_) => Less,
                Neg(otherform) => formula.cmp_structure(otherform),
                _ => Greater,
            },
            Formula::Imp(f1, f2) => match other {
                Bot | Var(_) | Neg(_) => Less,
                Imp(o1, o2) => match f1.cmp_structure(o1) {
                    Greater => Greater,
                    Less => Less,
                    Equal => f2.cmp_structure(o2),
                },
                _ => Greater,
            },
            Formula::And(f1, f2) => match other {
                Bot | Var(_) | Neg(_) | Imp(_, _) => Less,
                And(o1, o2) => match f1.cmp_structure(o1) {
                    Greater => Greater,
                    Less => Less,
                    Equal => f2.cmp_structure(o2),
                },
                _ => Greater,
            },
            Formula::Or(f1, f2) => match other {
                Bot | Var(_) | Neg(_) | Imp(_, _) | And(_, _) => Less,
                Or(o1, o2) => match f1.cmp_structure(o1) {
                    Greater => Greater,
                    Less => Less,
                    Equal => f2.cmp_structure(o2),
                },
            },
        }
    }

    fn get_free_vars(&self) -> Vec<u32> {
        // again this is terrible. atrocious code.
        match self {
            Formula::Bot => vec![],
            Formula::Neg(f1) => f1.get_free_vars(),
            Formula::Imp(f1, f2) => {
                let mut f1arr = f1.get_free_vars();
                f1arr.append(&mut f2.get_free_vars());
                f1arr
            }
            Formula::And(f1, f2) => {
                let mut f1arr = f1.get_free_vars();
                f1arr.append(&mut f2.get_free_vars());
                f1arr
            }
            Formula::Or(f1, f2) => {
                let mut f1arr = f1.get_free_vars();
                f1arr.append(&mut f2.get_free_vars());
                f1arr
            }
            Formula::Var(val) => vec![*val],
        }
    }
}

impl Add for Formula {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Formula::Or(Box::new(self), Box::new(rhs))
    }
}
impl Mul for Formula {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Formula::And(Box::new(self), Box::new(rhs))
    }
}
impl Shr for Formula {
    type Output = Self;
    fn shr(self, rhs: Self) -> Self::Output {
        Formula::Imp(Box::new(self), Box::new(rhs))
    }
}
impl Neg for Formula {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Formula::Neg(Box::new(self))
    }
}

impl std::fmt::Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Bot => write!(f, "⊥"),
            Formula::Var(i) => write!(f, "{}", var_to_char(*i)),
            Formula::Neg(formula) => write!(f, "¬{}", formula.to_string_parenth(self)),
            Formula::Imp(f1, f2) => write!(
                f,
                "{}⇒{}",
                f1.to_string_parenth(self),
                f2.to_string_parenth(self)
            ),
            Formula::And(f1, f2) => write!(
                f,
                "{}∧{}",
                f1.to_string_parenth(self),
                f2.to_string_parenth(self)
            ),
            Formula::Or(f1, f2) => write!(
                f,
                "{}∨{}",
                f1.to_string_parenth(self),
                f2.to_string_parenth(self)
            ),
        }
    }
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Ord for Formula {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_structure(other)
            .then(self.get_free_vars().cmp(&other.get_free_vars()))
    }
}

impl PartialOrd for Formula {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Formula {}
