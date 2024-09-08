use std::borrow::Borrow;

use rustsat::{clause, types::{Clause, Lit}};

// At most one
pub fn quadratic_amo<C, T>(literals: C) -> Vec<Clause>
where C: IntoIterator<Item = T>,
      T: Borrow<Lit>
{

    let lits = literals.into_iter().map(|c| *c.borrow()).collect::<Vec<_>>();
    let mut clauses = vec![];

    for (i, lit_a) in lits.iter().enumerate().skip(1) {
        for lit_b in lits.iter().take(i) {
            clauses.push(clause![!*lit_a, !*lit_b]);
        }
    }

    clauses
}

// One must be true
pub fn quadratic_one<C, T>(literals: C) -> Vec<Clause>
where C: IntoIterator<Item = T>,
      T: Borrow<Lit>
{
    let lits = literals.into_iter().map(|v| *v.borrow()).collect();
    let mut o = quadratic_amo(&lits);
    o.push(lits);
    o
}

