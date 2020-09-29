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

use crate::{FunctionInputVariableType, ResolvedNode, SymbolTable, Type, TypeError, VariableType};
use leo_typed::{FunctionInput, Identifier};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FunctionInputType {
    InputKeyword(Identifier),
    Variable(FunctionInputVariableType),
}

impl ResolvedNode for FunctionInputType {
    type Error = TypeError;
    type UnresolvedNode = FunctionInput;

    /// Type check a function input. Can be a typed variable or `input`.
    fn resolve(table: &mut SymbolTable, unresolved: Self::UnresolvedNode) -> Result<Self, Self::Error> {
        Ok(match unresolved {
            FunctionInput::InputKeyword(identifier) => FunctionInputType::InputKeyword(identifier),
            FunctionInput::Variable(variable) => {
                let variable_resolved = FunctionInputVariableType::resolve(table, variable)?;

                FunctionInputType::Variable(variable_resolved)
            }
        })
    }
}

impl FunctionInputType {
    pub fn identifier(&self) -> &Identifier {
        match self {
            FunctionInputType::InputKeyword(identifier) => identifier,
            FunctionInputType::Variable(variable) => &variable.identifier,
        }
    }

    pub fn type_(&self) -> &Type {
        match self {
            FunctionInputType::InputKeyword(_) => unimplemented!("ERROR: input type not implemented"),
            FunctionInputType::Variable(variable) => &variable.type_,
        }
    }

    /// Return a resolved function input from inside of a circuit
    pub fn from_circuit(
        table: &mut SymbolTable,
        unresolved: FunctionInput,
        circuit_name: Identifier,
    ) -> Result<Self, TypeError> {
        Ok(match unresolved {
            FunctionInput::InputKeyword(identifier) => FunctionInputType::InputKeyword(identifier),
            FunctionInput::Variable(unresolved_function_input) => {
                let function_input =
                    FunctionInputVariableType::from_circuit(table, unresolved_function_input, circuit_name)?;

                FunctionInputType::Variable(function_input)
            }
        })
    }

    /// Insert this function input into the given symbol table
    pub fn insert(&self, table: &mut SymbolTable) -> Option<VariableType> {
        match self {
            FunctionInputType::Variable(variable) => variable.insert(table),
            FunctionInputType::InputKeyword(_identifier) => {
                unimplemented!("uncomment when support for input types is added")
            }
        }
    }
}