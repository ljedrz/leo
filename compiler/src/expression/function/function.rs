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

//! Enforce a function call expression in a compiled Leo program.

use crate::{errors::ExpressionError, new_scope, program::ConstrainedProgram, value::ConstrainedValue, GroupType};
use leo_typed::{Expression, Span, Type};

use snarkos_models::{
    curves::{Field, PrimeField},
    gadgets::r1cs::ConstraintSystem,
};

impl<F: Field + PrimeField, G: GroupType<F>> ConstrainedProgram<F, G> {
    pub fn enforce_function_call_expression<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        file_scope: String,
        function_scope: String,
        expected_type: Option<Type>,
        function: Box<Expression>,
        arguments: Vec<Expression>,
        span: Span,
    ) -> Result<ConstrainedValue<F, G>, ExpressionError> {
        let (declared_circuit_reference, function_value) = match *function.clone() {
            Expression::CircuitMemberAccess(circuit_identifier, circuit_member, span) => {
                // Call a circuit function that can mutate self.

                // Save a reference to the circuit we are mutating.
                let circuit_id_string = format!("{}", circuit_identifier);
                let declared_circuit_reference = new_scope(function_scope.clone(), circuit_id_string);

                (
                    declared_circuit_reference,
                    self.enforce_circuit_access(
                        cs,
                        file_scope.clone(),
                        function_scope.clone(),
                        expected_type,
                        circuit_identifier,
                        circuit_member,
                        span,
                    )?,
                )
            }
            function => (
                function_scope.clone(),
                self.enforce_expression(cs, file_scope.clone(), function_scope.clone(), expected_type, function)?,
            ),
        };

        let (outer_scope, function_call) = function_value.extract_function(file_scope.clone(), span.clone())?;

        let name_unique = format!(
            "function call {} {}:{}",
            function_call.get_name(),
            span.line,
            span.start,
        );

        self.enforce_function(
            &mut cs.ns(|| name_unique),
            outer_scope,
            function_scope,
            function_call,
            arguments,
            declared_circuit_reference,
        )
        .map_err(|error| ExpressionError::from(Box::new(error)))
    }
}
