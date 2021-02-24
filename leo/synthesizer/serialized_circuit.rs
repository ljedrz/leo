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

use std::convert::TryFrom;

use serde::{Deserialize, Serialize};
use snarkvm_curves::bls12_377::Bls12_377;
use snarkvm_errors::curves::FieldError;
use snarkvm_models::{
    curves::PairingEngine,
    gadgets::r1cs::{ConstraintSystem, Index},
};

use crate::synthesizer::{CircuitSynthesizer, OptionalVec, SerializedField, SerializedIndex};

#[derive(Serialize, Deserialize)]
pub struct SerializedCircuit {
    pub num_inputs: usize,
    pub num_aux: usize,
    pub num_constraints: usize,

    pub input_assignment: Vec<SerializedField>,
    pub aux_assignment: Vec<SerializedField>,

    pub at: Vec<Vec<(SerializedField, SerializedIndex)>>,
    pub bt: Vec<Vec<(SerializedField, SerializedIndex)>>,
    pub ct: Vec<Vec<(SerializedField, SerializedIndex)>>,
}

impl SerializedCircuit {
    pub fn to_json_string(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self)
    }

    pub fn from_json_string(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

impl<E: PairingEngine> From<CircuitSynthesizer<E>> for SerializedCircuit {
    fn from(synthesizer: CircuitSynthesizer<E>) -> Self {
        let num_inputs = synthesizer.input_assignment.len();
        let num_aux = synthesizer.aux_assignment.len();
        let num_constraints = synthesizer.num_constraints();

        // Serialize assignments
        fn get_serialized_assignments<'a, E: PairingEngine, I: Iterator<Item = &'a E::Fr>>(
            assignments: I,
        ) -> Vec<SerializedField> {
            assignments.map(SerializedField::from).collect()
        }

        let input_assignment = get_serialized_assignments::<E, _>(synthesizer.input_assignment.iter());
        let aux_assignment = get_serialized_assignments::<E, _>(synthesizer.aux_assignment.iter());

        // Serialize constraints
        fn get_serialized_constraints<E: PairingEngine>(
            constraints: &[(E::Fr, Index)],
        ) -> Vec<(SerializedField, SerializedIndex)> {
            let mut serialized = Vec::with_capacity(constraints.len());

            for &(ref coeff, index) in constraints {
                let field = SerializedField::from(coeff);
                let index = SerializedIndex::from(index);

                serialized.push((field, index))
            }

            serialized
        }

        let mut at = Vec::with_capacity(num_constraints);
        let mut bt = Vec::with_capacity(num_constraints);
        let mut ct = Vec::with_capacity(num_constraints);

        for i in 0..num_constraints {
            // Serialize at[i]

            let a_constraints = get_serialized_constraints::<E>(&synthesizer.at[i]);
            at.push(a_constraints);

            // Serialize bt[i]

            let b_constraints = get_serialized_constraints::<E>(&synthesizer.bt[i]);
            bt.push(b_constraints);

            // Serialize ct[i]

            let c_constraints = get_serialized_constraints::<E>(&synthesizer.ct[i]);
            ct.push(c_constraints);
        }

        Self {
            num_inputs,
            num_aux,
            num_constraints,
            input_assignment,
            aux_assignment,
            at,
            bt,
            ct,
        }
    }
}

impl TryFrom<SerializedCircuit> for CircuitSynthesizer<Bls12_377> {
    type Error = FieldError;

    fn try_from(serialized: SerializedCircuit) -> Result<CircuitSynthesizer<Bls12_377>, Self::Error> {
        // Deserialize assignments
        fn get_deserialized_assignments(
            assignments: &[SerializedField],
        ) -> Result<OptionalVec<<Bls12_377 as PairingEngine>::Fr>, FieldError> {
            let mut deserialized = OptionalVec::with_capacity(assignments.len());

            for serialized_assignment in assignments {
                let field = <Bls12_377 as PairingEngine>::Fr::try_from(serialized_assignment)?;

                deserialized.insert(field);
            }

            Ok(deserialized)
        }

        let input_assignment = get_deserialized_assignments(&serialized.input_assignment)?;
        let aux_assignment = get_deserialized_assignments(&serialized.aux_assignment)?;

        // Deserialize constraints
        fn get_deserialized_constraints(
            constraints: &[(SerializedField, SerializedIndex)],
        ) -> Result<Vec<(<Bls12_377 as PairingEngine>::Fr, Index)>, FieldError> {
            let mut deserialized = Vec::with_capacity(constraints.len());

            for &(ref serialized_coeff, ref serialized_index) in constraints {
                let field = <Bls12_377 as PairingEngine>::Fr::try_from(serialized_coeff)?;
                let index = Index::from(serialized_index);

                deserialized.push((field, index));
            }

            Ok(deserialized)
        }

        let mut at = OptionalVec::with_capacity(serialized.num_constraints);
        let mut bt = OptionalVec::with_capacity(serialized.num_constraints);
        let mut ct = OptionalVec::with_capacity(serialized.num_constraints);

        for i in 0..serialized.num_constraints {
            // Deserialize at[i]

            let a_constraints = get_deserialized_constraints(&serialized.at[i])?;
            at.insert(a_constraints);

            // Deserialize bt[i]

            let b_constraints = get_deserialized_constraints(&serialized.bt[i])?;
            bt.insert(b_constraints);

            // Deserialize ct[i]

            let c_constraints = get_deserialized_constraints(&serialized.ct[i])?;
            ct.insert(c_constraints);
        }

        Ok(CircuitSynthesizer::<Bls12_377> {
            input_assignment,
            aux_assignment,
            at,
            bt,
            ct,
            namespaces: Default::default(),
        })
    }
}
