// Copyright (C) 2019-2020 Aleo Systems Inc.
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

//! Enforces a relational `==` operator in a resolved Leo program.

use crate::{enforce_and, errors::ExpressionError, value::ConstrainedValue, GroupType};
use leo_typed::Span;

use snarkos_models::{
    curves::{Field, PrimeField},
    gadgets::{
        r1cs::ConstraintSystem,
        utilities::{boolean::Boolean, eq::EvaluateEqGadget},
    },
};

pub fn evaluate_eq<F: Field + PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    left: ConstrainedValue<F, G>,
    right: ConstrainedValue<F, G>,
    span: Span,
) -> Result<ConstrainedValue<F, G>, ExpressionError> {
    let namespace_string = format!("evaluate {} == {} {}:{}", left, right, span.line, span.start);
    let error_string = format!("{} == {}", left, right);

    let constraint_result = match (left, right) {
        (ConstrainedValue::Address(address_1), ConstrainedValue::Address(address_2)) => {
            address_1.evaluate_equal(cs.ns(|| namespace_string), &address_2)
        }
        (ConstrainedValue::Boolean(bool_1), ConstrainedValue::Boolean(bool_2)) => {
            bool_1.evaluate_equal(cs.ns(|| namespace_string), &bool_2)
        }
        (ConstrainedValue::Integer(num_1), ConstrainedValue::Integer(num_2)) => {
            num_1.evaluate_equal(cs.ns(|| namespace_string), &num_2)
        }
        (ConstrainedValue::Field(field_1), ConstrainedValue::Field(field_2)) => {
            field_1.evaluate_equal(cs.ns(|| namespace_string), &field_2)
        }
        (ConstrainedValue::Group(point_1), ConstrainedValue::Group(point_2)) => {
            point_1.evaluate_equal(cs.ns(|| namespace_string), &point_2)
        }
        (ConstrainedValue::Array(arr_1), ConstrainedValue::Array(arr_2)) => {
            return evaluate_eq_multiple(&mut cs.ns(|| namespace_string), arr_1, arr_2, span);
        }
        (ConstrainedValue::Tuple(tuple_1), ConstrainedValue::Tuple(tuple_2)) => {
            return evaluate_eq_multiple(&mut cs.ns(|| namespace_string), tuple_1, tuple_2, span);
        }
        (
            ConstrainedValue::CircuitExpression(id_1, members_1),
            ConstrainedValue::CircuitExpression(id_2, members_2),
        ) => {
            // Return an error if we are trying to compare different circuits
            if id_1.ne(&id_2) {
                return Err(ExpressionError::incompatible_types(error_string, span.clone()));
            }

            let mut current = ConstrainedValue::Boolean(Boolean::constant(true));

            for (i, (left, right)) in members_1.into_iter().zip(members_2.into_iter()).enumerate() {
                let name_left = &left.0;
                let name_right = &right.0;
                if name_left.ne(&name_right) {
                    return Err(ExpressionError::incompatible_types(error_string, span.clone()));
                }

                let value_left = left.1;
                let value_right = right.1;

                let next = evaluate_eq(
                    &mut cs.ns(|| format!("tuple_index {}", i)),
                    value_left,
                    value_right,
                    span.clone(),
                )?;

                current = enforce_and(
                    &mut cs.ns(|| format!("tuple result {}", i)),
                    current,
                    next,
                    span.clone(),
                )?;
            }
            return Ok(current);
        }
        (ConstrainedValue::Unresolved(string), val_2) => {
            let val_1 = ConstrainedValue::from_other(string, &val_2, span.clone())?;
            return evaluate_eq(&mut cs.ns(|| namespace_string), val_1, val_2, span);
        }
        (val_1, ConstrainedValue::Unresolved(string)) => {
            let val_2 = ConstrainedValue::from_other(string, &val_1, span.clone())?;
            return evaluate_eq(&mut cs.ns(|| namespace_string), val_1, val_2, span);
        }
        (_, _) => {
            return Err(ExpressionError::incompatible_types(error_string, span));
        }
    };

    let boolean = constraint_result.map_err(|e| ExpressionError::cannot_enforce(format!("evaluate equal"), e, span))?;

    Ok(ConstrainedValue::Boolean(boolean))
}

pub fn evaluate_eq_multiple<F: Field + PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    left_vec: Vec<ConstrainedValue<F, G>>,
    right_vec: Vec<ConstrainedValue<F, G>>,
    span: Span,
) -> Result<ConstrainedValue<F, G>, ExpressionError> {
    let mut current = ConstrainedValue::Boolean(Boolean::constant(true));

    for (i, (left, right)) in left_vec.into_iter().zip(right_vec.into_iter()).enumerate() {
        let next = evaluate_eq(&mut cs.ns(|| format!("eq index {}", i)), left, right, span.clone())?;

        current = enforce_and(&mut cs.ns(|| format!("eq result {}", i)), current, next, span.clone())?;
    }

    return Ok(current);
}
