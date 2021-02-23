// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the Leo library.

// The Leo library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The Leo library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the Leo library. If not, see <https://www.gnu.org/licenses/>.

use snarkvm_errors::gadgets::SynthesisError;
use snarkvm_models::{
    curves::{Field, PairingEngine},
    gadgets::r1cs::{ConstraintSystem, Index, LinearCombination, Variable},
};

// a helper object containing a list of values that, when removed, leave a "hole" in their
// place; this allows all the following indices to remain unperturbed; the holes take priority
// when inserting new objects
#[derive(Default)]
pub struct OptionalVec<T> {
    // a list of optional values
    values: Vec<Option<T>>,
    // a list of indices of the Nones in the values vector
    holes: Vec<usize>,
}

impl<T> OptionalVec<T> {
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            values: Vec::with_capacity(cap),
            holes: Default::default(),
        }
    }

    // inserts a new value either into the first existing hole or extending the vector
    // of values, i.e. pushing it to its end
    #[inline]
    pub fn insert(&mut self, elem: T) -> usize {
        let idx = self.holes.pop().unwrap_or_else(|| self.values.len());
        if idx < self.values.len() {
            self.values[idx] = Some(elem);
        } else {
            self.values.push(Some(elem));
        }
        idx
    }

    // returns the index of the next value inserted into the OptionalVec
    #[inline]
    pub fn next_idx(&self) -> usize {
        self.holes.last().copied().unwrap_or_else(|| self.values.len())
    }

    // removes a value at the specified index; assumes that the index points to
    // an existing value that is a Some (i.e. not a hole)
    #[inline]
    pub fn remove(&mut self, idx: usize) -> T {
        let val = self.values[idx].take();
        self.holes.push(idx);
        val.unwrap()
    }

    // iterates over all the Some values in the list
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.values.iter().filter(|v| v.is_some()).map(|v| v.as_ref().unwrap())
    }

    // returns the number of the Some values
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len() - self.holes.len()
    }
}

impl<T> std::ops::Index<usize> for OptionalVec<T> {
    type Output = T;

    fn index(&self, idx: usize) -> &Self::Output {
        self.values[idx].as_ref().unwrap()
    }
}

impl<T> std::ops::IndexMut<usize> for OptionalVec<T> {
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        self.values[idx].as_mut().unwrap()
    }
}

#[derive(Default)]
pub struct Namespace {
    constraint_indices: Vec<usize>,
    input_indices: Vec<usize>,
    aux_indices: Vec<usize>,
}

pub struct CircuitSynthesizer<E: PairingEngine> {
    // Constraints
    pub(crate) at: OptionalVec<Vec<(E::Fr, Index)>>,
    pub(crate) bt: OptionalVec<Vec<(E::Fr, Index)>>,
    pub(crate) ct: OptionalVec<Vec<(E::Fr, Index)>>,

    // Assignments of variables
    pub(crate) input_assignment: OptionalVec<E::Fr>,
    pub(crate) aux_assignment: OptionalVec<E::Fr>,

    pub(crate) namespaces: Vec<Namespace>,
}

impl<E: PairingEngine> ConstraintSystem<E::Fr> for CircuitSynthesizer<E> {
    type Root = Self;

    #[inline]
    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: AsRef<str>,
    {
        let index = self.aux_assignment.len();
        self.aux_assignment.insert(f()?);
        if let Some(ref mut ns) = self.namespaces.last_mut() {
            ns.aux_indices.push(index);
        }
        Ok(Variable::new_unchecked(Index::Aux(index)))
    }

    #[inline]
    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: AsRef<str>,
    {
        let index = self.input_assignment.len();
        self.input_assignment.insert(f()?);
        if let Some(ref mut ns) = self.namespaces.last_mut() {
            ns.input_indices.push(index);
        }
        Ok(Variable::new_unchecked(Index::Input(index)))
    }

    #[inline]
    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: AsRef<str>,
        LA: FnOnce(LinearCombination<E::Fr>) -> LinearCombination<E::Fr>,
        LB: FnOnce(LinearCombination<E::Fr>) -> LinearCombination<E::Fr>,
        LC: FnOnce(LinearCombination<E::Fr>) -> LinearCombination<E::Fr>,
    {
        let num_constraints = self.num_constraints();

        self.at.insert(Vec::new());
        self.bt.insert(Vec::new());
        self.ct.insert(Vec::new());

        push_constraints(a(LinearCombination::zero()), &mut self.at, num_constraints);
        push_constraints(b(LinearCombination::zero()), &mut self.bt, num_constraints);
        push_constraints(c(LinearCombination::zero()), &mut self.ct, num_constraints);

        if let Some(ref mut ns) = self.namespaces.last_mut() {
            ns.constraint_indices.push(num_constraints);
        }
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: AsRef<str>,
        N: FnOnce() -> NR,
    {
        self.namespaces.push(Default::default());
    }

    fn pop_namespace(&mut self) {
        if let Some(ns) = self.namespaces.pop() {
            for idx in ns.constraint_indices {
                self.at.remove(idx);
                self.bt.remove(idx);
                self.ct.remove(idx);
            }

            for idx in ns.aux_indices {
                self.aux_assignment.remove(idx);
            }

            for idx in ns.input_indices {
                self.input_assignment.remove(idx);
            }
        }
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn num_constraints(&self) -> usize {
        self.at.len()
    }
}

fn push_constraints<F: Field>(
    l: LinearCombination<F>,
    constraints: &mut OptionalVec<Vec<(F, Index)>>,
    this_constraint: usize,
) {
    for (var, coeff) in l.as_ref() {
        match var.get_unchecked() {
            Index::Input(i) => constraints[this_constraint].push((*coeff, Index::Input(i))),
            Index::Aux(i) => constraints[this_constraint].push((*coeff, Index::Aux(i))),
        }
    }
}
