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

use pest::Span as AstSpan;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    /// text of input string
    pub text: String,
    /// program line
    pub line: usize,
    /// start column
    pub start: usize,
    /// end column
    pub end: usize,
}

impl<'ast> From<AstSpan<'ast>> for Span {
    fn from(span: AstSpan<'ast>) -> Self {
        let mut text = " ".to_string();
        let line_col = span.start_pos().line_col();
        let end = span.end_pos().line_col().1;

        text.push_str(span.start_pos().line_of().trim_end());

        Self {
            text,
            line: line_col.0,
            start: line_col.1,
            end,
        }
    }
}
