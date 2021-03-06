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

use crate::{errors::ImportError, ImportParser};
use leo_typed::Package;

pub static CORE_PACKAGE_NAME: &str = "core";

impl ImportParser {
    // import a core package into scope
    pub fn parse_core_package(&mut self, package: &Package) -> Result<(), ImportError> {
        self.insert_core_package(package);
        Ok(())
    }
}
