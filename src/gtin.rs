//! Parses and validates GTIN barcodes and its subsets
//!
//! # Examples
//!
//! ```rust
//! use gtin::{Gtin, GtinError};
//!
//! fn main() {
//!     let sample = Gtin::new("0010576000465").unwrap();
//!     assert_eq!(sample.to_string(), "0010576000465".to_string());
//!     
//!     // 12 digit codes are assumed to be UPC-A, and 2 zeros are padded to the beginning
//!     let upca_sample = Gtin::new("010576000465").unwrap();
//!     assert_eq!(upca_sample.to_string(), "0010576000465".to_string());
//!
//!     assert_eq!(Gtin::new("010576000466"), Err(GtinError::InvalidCheckDigit));
//! }
//! ```

use std::{
    fmt::{self, Debug},
    str::FromStr,
};

use serde::{Deserialize, Serialize};

/// Calculates the check digit for a GTIN based on the first 13 digits of the code. Useful for
/// validating codes
///
/// # Arguments
///
/// * `first_13` - The first 13 digits of the code to calculate a check digit for
///
/// # Returns
///
/// The appropriate check digit for the supplied code
pub fn calculate_check_digit(first_13: [u8; 13]) -> u8 {
    let sum_odd: u32 = first_13.iter().step_by(2).map(|&d| d as u32).sum();
    let sum_even: u32 = first_13.iter().skip(1).step_by(2).map(|&d| d as u32).sum();
    let total = sum_odd * 3 + sum_even;
    let mut check = total % 10;
    if check != 0 {
        check = 10 - check;
    }
    check as u8
}

/// Errors that occur when validating a code
#[derive(Debug, PartialEq, Eq)]
pub enum GtinError {
    /// Occurs when a code is not exactly 13 digits long. (Or 12 digits as a preceding 0 is assumed)
    InvalidLength,

    /// There is a character in the code that is not 0-9
    InvalidDigit,

    /// The check digit of the supplied code is incorrect
    InvalidCheckDigit,
}

impl fmt::Display for GtinError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCheckDigit => {
                write!(
                    f,
                    "Attempted to generate a GTIN with an invalid check digit"
                )
            }
            Self::InvalidDigit => {
                write!(
                    f,
                    "Attempted to generate a GTIN with non numeric characters"
                )
            }
            Self::InvalidLength => {
                write!(f, "Attempted to generate a GTIN with a bad length")
            }
        }
    }
}

impl std::error::Error for GtinError {}

/// Represents a validated GTIN barcode
#[derive(Clone, PartialEq, Eq, Hash, Copy)]
pub struct Gtin {
    digits: [u8; 14],
    kind: GtinKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum GtinKind {
    Gtin8,
    Gtin12,
    Gtin13,
    Gtin14,
}

impl Debug for Gtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Gtin(digits: {}, kind: {:?})",
            self.to_string(),
            self.kind
        )
    }
}

impl Gtin {
    /// Attempts to parse &str into a GTIN
    ///
    /// # Arguments
    ///
    /// * `input` - The string that represents the code to validate
    ///
    /// # Returns
    ///
    /// * A valid [`Gtin`] if successful. Otherwise, return an [`Error`]
    ///
    /// # Errors
    ///
    /// Returns a member of [`GtinError`] if the length of the supplied code is not either 14, 13,
    /// 12, or 8 corresponding to GTIN-14, GTIN-13, GTIN-12, or GTIN-8
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gtin::Gtin;
    ///
    /// let valid = Gtin::new("706285102001").unwrap();
    /// assert_eq!(valid.to_string(), "00706285102001".to_string());
    /// ```
    pub fn new(input: &str) -> Result<Self, GtinError> {
        let (full_length, kind) = match input.len() {
            8 => (format!("000000{}", input), GtinKind::Gtin8),
            12 => (
                format!("00{}", input),
                if &input[..4] == "0000" {
                    GtinKind::Gtin8
                } else {
                    GtinKind::Gtin12
                },
            ),
            13 => (
                format!("0{}", input),
                if &input[..5] == "00000" {
                    GtinKind::Gtin8
                } else if &input[..1] == "0" {
                    GtinKind::Gtin12
                } else {
                    GtinKind::Gtin13
                },
            ),
            14 => (
                input.to_string(),
                if &input[..6] == "000000" {
                    GtinKind::Gtin8
                } else if &input[..2] == "00" {
                    GtinKind::Gtin12
                } else if &input[..1] == "0" {
                    GtinKind::Gtin13
                } else {
                    GtinKind::Gtin14
                },
            ),
            _ => return Err(GtinError::InvalidLength),
        };

        let mut digits = [0u8; 14];
        for (i, ch) in full_length.chars().enumerate() {
            digits[i] = ch
                .to_digit(10)
                .ok_or(GtinError::InvalidDigit)?
                .try_into()
                .or(Err(GtinError::InvalidDigit))?;
        }

        // Validate check digit
        let first_13: [u8; 13] = digits[0..13].try_into().or(Err(GtinError::InvalidLength))?;
        let expected = calculate_check_digit(first_13);
        let actual = digits[13];
        if expected != actual {
            return Err(GtinError::InvalidCheckDigit);
        }

        Ok(Self { digits, kind })
    }

    /// Represents the code as an array of 13 u8 digits
    pub fn as_arr(&self) -> [u8; 14] {
        self.digits.clone()
    }

    pub fn kind(&self) -> GtinKind {
        self.kind
    }

    pub fn normalize_digits(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for Gtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl FromStr for Gtin {
    type Err = GtinError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl Serialize for Gtin {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for Gtin {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Gtin::new(&s).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Gtin, GtinError, gtin::calculate_check_digit};

    #[test]
    fn test_serialize() {
        let upc = Gtin::new("041303015070").unwrap();
        let json = serde_json::json!({"upc": upc});
        assert_eq!(json.to_string(), r#"{"upc":"0041303015070"}"#);
    }

    #[test]
    fn test_deserialize() {
        let deserialized: Gtin = serde_json::from_str("\"041303015070\"").unwrap();
        assert_eq!(deserialized, Gtin::new("041303015070").unwrap());
    }

    #[test]
    fn test_display() {
        assert_eq!(
            format!("{}", Gtin::new("041303015070").unwrap()),
            "GTIN(0041303015070)"
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(
            Gtin::new("0041303015070").unwrap().to_string(),
            "0041303015070".to_string()
        );
    }

    #[test]
    fn test_calculate_check_digit() {
        let valids = [
            ("004130301507", 0u8),
            ("007797509512", 6),
            ("073803920906", 3),
            ("001410005297", 5),
            ("080882908146", 6),
            ("080812411166", 0),
            ("934071000250", 7),
            ("934071000251", 4),
            ("934071000241", 5),
        ];

        for (upc, check) in valids {
            let first_12: [u8; 12] = upc
                .chars()
                .map(|c| c.to_digit(10).unwrap() as u8)
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap();
            assert_eq!(calculate_check_digit(first_12), check);
        }
    }

    #[test]
    fn test_new() {
        assert!(Gtin::new("0000000000000").is_ok());
        assert!(Gtin::new("9340710002507").is_ok());
        assert!(Gtin::new("9340710002415").is_ok());
        assert!(Gtin::new("9340710002514").is_ok());
        assert_eq!(Gtin::new(""), Err(GtinError::InvalidLength));
        assert_eq!(Gtin::new("041303015071"), Err(GtinError::InvalidCheckDigit));
        assert_eq!(
            Gtin::new("0041303015071"),
            Err(GtinError::InvalidCheckDigit)
        );
        assert!(Gtin::new("0703948501157").is_ok());
        assert_eq!(Gtin::new("00413b3015071"), Err(GtinError::InvalidDigit));
    }

    #[test]
    fn test_from_str_nonstrict() {
        // All non-numeric characters are ignored
        assert_eq!(
            Gtin::from_str_nonstrict("a761458256240").unwrap(),
            Gtin::new("0761458256240").unwrap()
        );

        // Codes shorter than 13 digits will be forward padded with zeros until their length is 13
        assert_eq!(
            Gtin::from_str_nonstrict("1234565").unwrap(),
            Gtin::new("0000001234565").unwrap()
        );

        // Codes longer than 13 characters without any preceeding zeros will still fail to generate
        assert_eq!(
            Gtin::from_str_nonstrict("12345678901234"),
            Err(GtinError::InvalidLength)
        );

        // Codes longer than 13 digits with preceeding zeros will have preceeding zeros truncated
        assert_eq!(
            Gtin::from_str_nonstrict("00000000001234565").unwrap(),
            Gtin::new("0000001234565").unwrap()
        );

        // Codes with an incorrect check digit will have their check digit fixed
        assert_eq!(
            Gtin::from_str_nonstrict("0000001234566").unwrap(),
            Gtin::new("0000001234565").unwrap()
        );

        // Be very careful! Strings that are not close to barcodes at all may still result in valid
        // looking [`Gtin`]s
        assert_eq!(
            Gtin::from_str_nonstrict("absolute nonsense").unwrap(),
            Gtin::new("0000000000000").unwrap()
        );

        assert_eq!(
            Gtin::from_str_nonstrict("9340710002515").unwrap(),
            Gtin::new("9340710002514").unwrap()
        );
        assert_eq!(
            Gtin::from_str_nonstrict("9340710002507").unwrap(),
            Gtin::new("9340710002507").unwrap()
        );
        assert_eq!(
            Gtin::from_str_nonstrict("9340710002415").unwrap(),
            Gtin::new("9340710002415").unwrap()
        );
    }

    #[test]
    fn test_as_arr() {
        assert_eq!(
            Gtin::new("706285102001").unwrap().as_arr(),
            [0, 7, 0, 6, 2, 8, 5, 1, 0, 2, 0, 0, 1]
        );
    }

    #[test]
    fn test_is_upca() {
        assert!(Gtin::new("0041303015070").unwrap().is_upca());
        assert!(!Gtin::new("6936685222021").unwrap().is_upca());
    }

    #[test]
    fn test_to_upca_string() {
        assert_eq!(
            Gtin::new("0041303015070").unwrap().normalize_digits(),
            "041303015070".to_string()
        );
        assert_eq!(
            Gtin::new("6936685222021").unwrap().normalize_digits(),
            "6936685222021".to_string()
        );
    }

    #[test]
    fn test_default() {
        assert_eq!(Gtin::default(), Gtin::new("0000000000000").unwrap());
    }
}
