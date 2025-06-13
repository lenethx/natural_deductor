enum Formula {
    Bot,
    Var(u32), 
    Neg(Box<Self>),
    Imp(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

struct Sequent {
    context:Vec<Formula>,
    rest:Formula
}

struct Proof {
    root: Sequent,
    rule: Option<Box<Rule>>
    
}

impl Proof {
    fn size(&self)->u32 {
        
    }
}

enum Rule {
    Ax,
    AndE1(Box<Proof>),
    AndE2(Box<Proof>),
    AndI(Box<Proof>, Box<Proof>),
    ImpI(Box<Proof>),
    ImpE(Box<Proof>, Box<Proof>),
    OrI1(Box<Proof>),
    OrI2(Box<Proof>),
    OrE(Box<Proof>, Box<Proof>, Box<Proof>),
    BotE(Box<Proof>),
    NegE(Box<Proof>, Box<Proof>),
    NegI(Box<Proof>),
    NegNegI(Box<Proof>),
    MT(Box<Proof>, Box<Proof>),
    LEM,
    NegNegE(Box<Proof>),
    PBC(Box<Proof>),
}


fn main() {
    let formulaToProve = Sequent{
        context:vec![Formula::Var(1), Formula::Imp(Box::new(Formula::Var(1)),Box::new(Formula::Var(2)) )], 
        rest: Formula::Var(2)
    };

    let proof = Proof{root: formulaToProve, rule:None};
    loop {
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

    
    
}
