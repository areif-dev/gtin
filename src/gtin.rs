//! Parses and validates GTIN barcodes and its subsets
//!
//! # Examples
//!
//! ```rust
//! use gtin::{Gtin, GtinError};
//!
//! fn main() {
//!     let sample = Gtin::new("0010576000465").unwrap();
//!     assert_eq!(sample.to_string(), "00010576000465".to_string());
//!     
//!     // 12 digit codes are assumed to be UPC-A, and 2 zeros are padded to the beginning
//!     let upca_sample = Gtin::new("010576000465").unwrap();
//!     assert_eq!(upca_sample.to_string(), "00010576000465".to_string());
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
/// The calculation uses the standard weighted sum algorithm:
/// 1. Sum the digits at odd positions (1st, 3rd, 5th, etc.).
/// 2. Sum the digits at even positions (2nd, 4th, 6th, etc.).
/// 3. Calculate `(SumOdd * 3) + SumEven`.
/// 4. The check digit is the smallest number added to the total to make it a multiple of 10.
///
/// # Arguments
///
/// * `first_13` - The first 13 digits of the code to calculate a check digit for (as an array of `u8`)
///
/// # Returns
///
/// The appropriate check digit for the supplied code
///
/// # Examples
///
/// The first 13 digits of a code `0001057600046` result in a check digit of `5`.
///
/// ```rust
/// use gtin::calculate_check_digit;
///
/// // Example of a GTIN-13 code (without the check digit)
/// // Digits: 0 0 0 1 0 5 7 6 0 0 0 4 6 5
/// // (The actual code is 00010576000465, but we provide only the first 13 digits)
/// let first_13_digits: [u8; 13] = [0, 0, 0, 1, 0, 5, 7, 6, 0, 0, 0, 4, 6];
/// let check_digit = calculate_check_digit(first_13_digits);
///
/// assert_eq!(check_digit, 5);
/// ```
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
    /// Occurs when the length of the supplied code is not one of 8, 12, 13, or 14
    InvalidLength,

    /// There is a character in the code that is not 0-9
    InvalidCharacter,

    /// The check digit of the supplied code is incorrect
    InvalidCheckDigit,
}

/// Represents the specific standard/format of the GTIN code.
///
/// A GTIN code is always internally stored as 14 digits, but its "Kind"
/// denotes the original standard it conforms to, which is defined by its
/// effective length (8, 12, 13, or 14 digits).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum GtinKind {
    /// Global Trade Item Number - 8 digits (equivalent to EAN-8).
    ///
    /// This is stored internally as a 14-digit code with six leading zeros.
    Gtin8,
    /// Global Trade Item Number - 12 digits (equivalent to UPC-A).
    ///
    /// This is stored internally as a 14-digit code with two leading zeros.
    Gtin12,
    /// Global Trade Item Number - 13 digits (equivalent to EAN-13).
    ///
    /// This is stored internally as a 14-digit code with one leading zero.
    Gtin13,
    /// Global Trade Item Number - 14 digits (often used for trade/shipping units).
    ///
    /// This is stored internally as the full 14-digit code.
    Gtin14,
}

/// Represents a validated GTIN barcode
#[derive(Clone, PartialEq, Eq, Hash, Copy)]
pub struct Gtin {
    digits: [u8; 14],
    kind: GtinKind,
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
            Self::InvalidCharacter => {
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
    /// Attempts to parse a GTIN from `&str`
    ///
    /// # Arguments
    ///
    /// * `input` - The string that represents the code to validate
    ///
    /// # Returns
    ///
    /// * A valid [`Gtin`] if successful. Otherwise, return a [`GtinError`]
    ///
    /// # Errors
    ///
    /// * [`GtinError::InvalidLength`] if the length of `input` is not 8, 12, 13, or 14
    /// * [`GtinError::InvalidCharacter`] if any character of `input` is not a digit 0-9
    /// * [`GtinError::InvalidCheckDigit`] if `input` does not have a valid check digit
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
                .ok_or(GtinError::InvalidCharacter)?
                .try_into()
                .or(Err(GtinError::InvalidCharacter))?;
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

    /// Returns the GTIN code as an array of 14 `u8` digits.
    ///
    /// This array always contains the full 14-digit GTIN representation,
    /// including any leading zeros that were prepended to the code
    /// from its original length (8, 12, or 13 digits).
    ///
    /// # Returns
    ///
    /// The 14-digit GTIN code as a fixed-size array `[u8; 14]`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gtin::Gtin;
    ///
    /// // Input is a 12-digit UPC-A (GTIN-12), which gets padded with two leading zeros: "00".
    /// let gtin_12 = Gtin::new("010576000465").unwrap();
    ///
    /// // The resulting 14-digit array is:
    /// let expected_arr: [u8; 14] = [0, 0, 0, 1, 0, 5, 7, 6, 0, 0, 0, 4, 6, 5];
    ///
    /// assert_eq!(gtin_12.as_arr(), expected_arr);
    /// ```
    pub fn as_arr(&self) -> [u8; 14] {
        self.digits.clone()
    }

    /// Returns the specific kind of GTIN (GTIN-8, GTIN-12, GTIN-13, or GTIN-14)
    /// based on the number of leading zeros in the 14-digit representation.
    ///
    /// # Returns
    ///
    /// The [`GtinKind`] variant corresponding to the original code structure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gtin::{Gtin, GtinKind};
    ///
    /// // A 12-digit UPC-A code is stored as GTIN-12
    /// let gtin_12 = Gtin::new("010576000465").unwrap();
    /// assert_eq!(gtin_12.kind(), GtinKind::Gtin12);
    ///
    /// // A 13-digit EAN-13 code is stored as GTIN-13
    /// let gtin_13 = Gtin::new("9506000140445").unwrap();
    /// assert_eq!(gtin_13.kind(), GtinKind::Gtin13);
    /// ```
    pub fn kind(&self) -> GtinKind {
        self.kind
    }

    /// Returns the GTIN digits as a `String`, stripped of any leading zeros
    /// that were padded during creation to meet the 14-digit format.
    ///
    /// This effectively returns the code in its original length (8, 12, 13, or 14 digits)
    /// based on its [`GtinKind`].
    ///
    /// # Returns
    ///
    /// A `String` containing the original, un-padded digits of the GTIN code.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gtin::Gtin;
    ///
    /// // A 12-digit code normalized to 12 digits
    /// let upca = Gtin::new("010576000465").unwrap();
    /// assert_eq!(upca.to_string(), "00010576000465".to_string()); // Full 14-digit display
    /// assert_eq!(upca.normalize_digits(), "010576000465".to_string()); // Original length
    ///
    /// // A 8-digit code normalized to 8 digits
    /// let gtin8 = Gtin::new("40000008").unwrap();
    /// assert_eq!(gtin8.to_string(), "00000040000008".to_string()); // Full 14-digit display
    /// assert_eq!(gtin8.normalize_digits(), "40000008".to_string()); // Original length
    /// ```
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
