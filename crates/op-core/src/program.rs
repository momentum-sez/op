//! Versioned authored programs with an explicit purpose.

use std::fmt;

use serde::{
    de::{value::MapAccessDeserializer, MapAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};

use crate::{parser::validate_program, typecheck_program, OpError, OpProgram};

pub use mez_canonical::{ProgramPurposeTag, ProgramPurposeTagError};

/// A checked Op program with its required, case-sensitive authored purpose.
///
/// The wire object requires `version: 1`, `purpose`, and `program`.
/// Human-readable formats require an object with named fields.
/// Validation uses the existing structural and type checks on the inner AST.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AuthoredOpProgramV1 {
    version: u32,
    purpose: ProgramPurposeTag,
    program: OpProgram,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuthoredOpProgramV1Wire {
    version: u32,
    purpose: ProgramPurposeTag,
    program: OpProgram,
}

impl<'de> Deserialize<'de> for AuthoredOpProgramV1 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = if deserializer.is_human_readable() {
            deserializer.deserialize_map(AuthoredOpProgramV1MapVisitor)?
        } else {
            AuthoredOpProgramV1Wire::deserialize(deserializer)?
        };
        wire.try_into().map_err(serde::de::Error::custom)
    }
}

struct AuthoredOpProgramV1MapVisitor;

impl<'de> Visitor<'de> for AuthoredOpProgramV1MapVisitor {
    type Value = AuthoredOpProgramV1Wire;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("an authored Op program object")
    }

    fn visit_map<M: MapAccess<'de>>(self, map: M) -> Result<Self::Value, M::Error> {
        AuthoredOpProgramV1Wire::deserialize(MapAccessDeserializer::new(map))
    }
}

impl TryFrom<AuthoredOpProgramV1Wire> for AuthoredOpProgramV1 {
    type Error = OpError;

    fn try_from(wire: AuthoredOpProgramV1Wire) -> Result<Self, Self::Error> {
        if wire.version != 1 {
            return Err(OpError::ParseError {
                line: 0,
                message: format!("unsupported authored Op program version: {}", wire.version),
            });
        }
        Self::new(wire.purpose, wire.program)
    }
}

impl AuthoredOpProgramV1 {
    /// Check the supplied program and retain its exact authored purpose.
    pub fn new(purpose: ProgramPurposeTag, program: OpProgram) -> Result<Self, OpError> {
        validate_program(&program)?;
        let checked = typecheck_program(&program);
        if !checked.success {
            return Err(OpError::TypeError(checked.errors.join("; ")));
        }
        Ok(Self {
            version: 1,
            purpose,
            program,
        })
    }

    /// Return the exact authored purpose.
    pub fn purpose(&self) -> &ProgramPurposeTag {
        &self.purpose
    }

    /// Return the checked inner AST.
    pub fn program(&self) -> &OpProgram {
        &self.program
    }

    /// Return both the authored purpose and the inner AST.
    pub fn into_parts(self) -> (ProgramPurposeTag, OpProgram) {
        (self.purpose, self.program)
    }
}
