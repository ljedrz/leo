use crate::InputValueError;

use snarkos_errors::{algorithms::CommitmentError, objects::account::AccountError};

use std::{io::Error as IOError, num::ParseIntError, str::ParseBoolError};

#[derive(Debug, Error)]
pub enum RecordVerificationError {
    #[error("{}", _0)]
    AccountError(#[from] AccountError),

    #[error("record commitment does not match record data")]
    CommitmentsDoNotMatch,

    #[error("{}", _0)]
    CommitmentError(#[from] CommitmentError),

    #[error("{}", _0)]
    InputValueError(#[from] InputValueError),

    #[error("{}", _0)]
    IOError(#[from] IOError),

    #[error("record parameter `{}` not found in state file", _0)]
    MissingParameter(String),

    #[error("{}", _0)]
    ParseBoolError(#[from] ParseBoolError),

    #[error("{}", _0)]
    ParseIntError(#[from] ParseIntError),
}