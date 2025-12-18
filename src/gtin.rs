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
    pub fn new(code: &str) -> Result<Self, GtinError> {
        let full_length = match code.len() {
            8 => format!("000000{}", code),
            12 => format!("00{}", code),
            13 => format!("0{}", code),
            14 => code.to_string(),
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

        let kind = if digits[..6] == [0; 6] {
            GtinKind::Gtin8
        } else if digits[..2] == [0; 2] {
            GtinKind::Gtin12
        } else if digits[..1] == [0] {
            GtinKind::Gtin13
        } else {
            GtinKind::Gtin14
        };

        Ok(Self { digits, kind })
    }

    /// Attempts to construct a GTIN by cleaning and strictly validating the last 14 digits found in the input string.
    ///
    /// This "non-strict" constructor attempts to clean and format the input string in a very forgiving way:
    ///
    /// 1. Filters: It ignores all non-digit characters in the input string.
    /// 2. Truncates: It takes only the last 14 consecutive digits found in the remaining digits.
    /// 3. Pads (If necessary): If fewer than 14 digits remain, it prepends leading zeros until it has 14 digits.
    /// 4. Calculates Check Digit: It recalculates the check digit based on the first 13 digits of the resulting 14-digit code.
    /// 5. Final Construction: It uses the newly calculated check digit and the first 13 digits to form a valid GTIN-14 code.
    ///
    /// # Warning
    /// This function is intended for inputs that are visually messy (e.g., "0-105-7600-046-5" or "GTIN 010576000465").
    /// It does not validate the original input's check digit. If the original code had a valid check digit, it will be
    /// overwritten by the recalculated check digit in the output. This can lead to a different GTIN than the one
    /// intended by the user if the original check digit was incorrect or missing.
    ///
    /// Prefer using [`Gtin::new`] for strict validation.
    ///
    /// # Arguments
    ///
    /// * `nonstrict_code` - A potentially messy string that is expected to contain a GTIN.
    ///
    /// # Returns
    ///
    /// A valid [`Gtin`] object that conforms to the GTIN-14 standard, derived from the input.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gtin::Gtin;
    ///
    /// // 1. Input with non-numeric characters and spaces (12-digit code).
    /// let messy_input = Gtin::nonstrict_new("0-105 7600-046-5"); // cleans to "00010576000465"
    /// assert_eq!(messy_input.to_string(), "00010576000465".to_string());
    ///
    /// // 2. Input that is too long (only the last 14 digits are kept).
    /// // The last 14 digits are: 01234567890128
    /// let too_long = Gtin::nonstrict_new("112233445501234567890128");
    /// assert_eq!(too_long.to_string(), "01234567890128".to_string());
    ///
    /// // 3. Input with an invalid check digit is fixed.
    /// // Original 13 digits: 1234567890123. The correct check digit is 1.
    /// // The input has a 9 as the last digit, but the function forces a 1.
    /// let invalid_code = Gtin::nonstrict_new("12345678901239");
    /// assert_eq!(invalid_code.to_string(), "12345678901231".to_string());
    /// ```
    ///
    /// # Panics
    ///
    /// This function will panic if the final, cleaned, and padded 14-digit string fails to be
    /// parsed by [`Gtin::new`]. This should only happen if there is an internal logic error,
    /// as `nonstrict_new` is designed to always produce a syntactically valid GTIN-14 string
    /// with a guaranteed correct check digit.
    pub fn nonstrict_new(nonstrict_code: &str) -> Self {
        let only_digits: Vec<u8> = nonstrict_code
            .chars()
            .filter_map(|c| c.to_string().parse::<u8>().ok())
            .collect();
        let mut last_14_digits: Vec<u8> = only_digits.into_iter().rev().take(14).collect();
        for _ in 0..(14 - last_14_digits.len()) {
            last_14_digits.push(0);
        }
        last_14_digits.reverse();
        let mut first_13 = [0u8; 13];
        for (i, d) in last_14_digits.iter().enumerate() {
            if i >= 13 {
                break;
            }
            first_13[i] = *d;
        }
        let check_digit = calculate_check_digit(first_13);
        let code = format!(
            "{}{}",
            first_13.iter().map(|d| d.to_string()).collect::<String>(),
            check_digit
        );
        Self::new(&code).expect("Failed to generate a valid GTIN from provided input")
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
    /// assert_eq!(upca.to_string_no_padding(), "010576000465".to_string()); // Original length
    ///
    /// // A 8-digit code normalized to 8 digits
    /// let gtin8 = Gtin::new("40000008").unwrap();
    /// assert_eq!(gtin8.to_string(), "00000040000008".to_string()); // Full 14-digit display
    /// assert_eq!(gtin8.to_string_no_padding(), "40000008".to_string()); // Original length
    /// ```
    pub fn to_string_no_padding(&self) -> String {
        match self.kind() {
            GtinKind::Gtin8 => self.digits[6..].iter().map(|d| d.to_string()).collect(),
            GtinKind::Gtin12 => self.digits[2..].iter().map(|d| d.to_string()).collect(),
            GtinKind::Gtin13 => self.digits[1..].iter().map(|d| d.to_string()).collect(),
            GtinKind::Gtin14 => self.digits.iter().map(|d| d.to_string()).collect(),
        }
    }
}

impl fmt::Display for Gtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.digits
                .iter()
                .map(|d| d.to_string())
                .collect::<String>()
        )
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
    use serde::Deserialize;
    use std::{collections::HashMap, str::FromStr};

    use crate::{
        Gtin, GtinError,
        gtin::{GtinKind, calculate_check_digit},
    };

    fn sample_gtins() -> HashMap<GtinKind, Vec<(Gtin, String)>> {
        let map = HashMap::from([
            (
                GtinKind::Gtin12,
                vec![
                    (
                        Gtin::new("082657543338").unwrap(),
                        String::from("082657543338"),
                    ),
                    (
                        Gtin::new("0037083062113").unwrap(),
                        String::from("0037083062113"),
                    ),
                    (
                        Gtin::new("037083062311").unwrap(),
                        String::from("037083062311"),
                    ),
                    (
                        Gtin::new("00037083063196").unwrap(),
                        String::from("00037083063196"),
                    ),
                    (
                        Gtin::new("0041540303763").unwrap(),
                        String::from("0041540303763"),
                    ),
                    (
                        Gtin::new("032076938130").unwrap(),
                        String::from("032076938130"),
                    ),
                    (
                        Gtin::new("00032076938147").unwrap(),
                        String::from("00032076938147"),
                    ),
                    (
                        Gtin::new("795711340001").unwrap(),
                        String::from("795711340001"),
                    ),
                ],
            ),
            (
                GtinKind::Gtin13,
                vec![
                    (
                        Gtin::new("4059433692142").unwrap(),
                        String::from("4059433692142"),
                    ),
                    (
                        Gtin::new("5038083603370").unwrap(),
                        String::from("5038083603370"),
                    ),
                    (
                        Gtin::new("05051771685816").unwrap(),
                        String::from("05051771685816"),
                    ),
                    (
                        Gtin::new("04059433537863").unwrap(),
                        String::from("04059433537863"),
                    ),
                    (
                        Gtin::new("4055744029608").unwrap(),
                        String::from("4055744029608"),
                    ),
                    (
                        Gtin::new("04055744029615").unwrap(),
                        String::from("04055744029615"),
                    ),
                    (
                        Gtin::new("9340710002422").unwrap(),
                        String::from("9340710002422"),
                    ),
                    (
                        Gtin::new("09340710002484").unwrap(),
                        String::from("09340710002484"),
                    ),
                ],
            ),
            (
                GtinKind::Gtin8,
                vec![
                    (Gtin::new("12345670").unwrap(), String::from("12345670")),
                    (Gtin::new("76543210").unwrap(), String::from("76543210")),
                    (Gtin::new("32214987").unwrap(), String::from("32214987")),
                    (Gtin::new("65498712").unwrap(), String::from("65498712")),
                    (Gtin::new("15607652").unwrap(), String::from("15607652")),
                    (Gtin::new("16784093").unwrap(), String::from("16784093")),
                    (Gtin::new("50287895").unwrap(), String::from("50287895")),
                    (Gtin::new("49215403").unwrap(), String::from("49215403")),
                ],
            ),
            (
                GtinKind::Gtin14,
                vec![
                    (
                        Gtin::new("10082657543335").unwrap(),
                        String::from("10082657543335"),
                    ),
                    (
                        Gtin::new("30037083063197").unwrap(),
                        String::from("30037083063197"),
                    ),
                    (
                        Gtin::new("10037083062110").unwrap(),
                        String::from("10037083062110"),
                    ),
                    (
                        Gtin::new("20037083062315").unwrap(),
                        String::from("20037083062315"),
                    ),
                    (
                        Gtin::new("50070257509583").unwrap(),
                        String::from("50070257509583"),
                    ),
                    (
                        Gtin::new("60041540303765").unwrap(),
                        String::from("60041540303765"),
                    ),
                    (
                        Gtin::new("10795711340008").unwrap(),
                        String::from("10795711340008"),
                    ),
                    (
                        Gtin::new("14055744029605").unwrap(),
                        String::from("14055744029605"),
                    ),
                ],
            ),
        ]);

        for (kind, list) in map.iter() {
            for (gtin, code) in list {
                assert_eq!(*kind, gtin.kind());
            }
        }
        map
    }

    #[test]
    fn test_calculate_check_digit() {
        let samples = sample_gtins();
        for (_, gtins_and_codes) in samples {
            for (_, code) in gtins_and_codes {
                let mut digits = [0u8; 13];
                for (i, char) in code.chars().rev().skip(1).enumerate() {
                    digits[12 - i] = char.to_digit(10).unwrap().try_into().unwrap();
                }
                let expected_check_digit = calculate_check_digit(digits);
                let actual_check_digit: u8 = code
                    .chars()
                    .last()
                    .unwrap()
                    .to_digit(10)
                    .unwrap()
                    .try_into()
                    .unwrap();
                assert_eq!(expected_check_digit, actual_check_digit);
            }
        }
    }

    #[test]
    fn test_new() {
        let _ = sample_gtins();
        assert_eq!(Gtin::new(""), Err(GtinError::InvalidLength));
        assert_eq!(Gtin::new("041303015071"), Err(GtinError::InvalidCheckDigit));
        assert_eq!(
            Gtin::new("0041303015071"),
            Err(GtinError::InvalidCheckDigit)
        );
        assert_eq!(Gtin::new("00413b3015071"), Err(GtinError::InvalidCharacter));
        assert_eq!(Gtin::new("123456789012345"), Err(GtinError::InvalidLength));
    }

    #[test]
    fn test_nonstrict_new() {
        let samples = sample_gtins();
        for (_kind, gtins_and_codes) in samples {
            for (gtin, code) in gtins_and_codes {
                assert_eq!(Gtin::nonstrict_new(&code), gtin);
            }
        }
        assert_eq!(
            Gtin::nonstrict_new(""),
            Gtin::new("00000000000000").unwrap()
        );
        assert_eq!(
            Gtin::nonstrict_new("A12345678901"),
            Gtin::new("00012345678905").unwrap()
        );
        assert_eq!(
            Gtin::nonstrict_new("abcdefghijklmn"),
            Gtin::new("00000000000000").unwrap()
        );
        assert_eq!(
            Gtin::nonstrict_new("00000f12345678"),
            Gtin::new("00000012345670").unwrap()
        );
        assert_eq!(
            Gtin::nonstrict_new("123456789012345678901234567890"),
            Gtin::new("78901234567899").unwrap()
        );
        assert_eq!(
            Gtin::nonstrict_new("98765432101234"),
            Gtin::new("98765432101231").unwrap()
        );
    }

    #[test]
    fn test_as_arr() {
        let samples = sample_gtins();
        for (_, gtins_and_codes) in samples {
            for (gtin, code) in gtins_and_codes {
                let mut digits_from_code = [0u8; 14];
                for (i, char) in code.chars().enumerate() {
                    digits_from_code[i + (14 - code.len())] =
                        char.to_digit(10).unwrap().try_into().unwrap();
                }
                assert_eq!(gtin.as_arr(), digits_from_code);
            }
        }
    }

    #[test]
    fn test_to_string_no_padding() {
        let samples = sample_gtins();
        for (kind, gtins_and_codes) in samples {
            for (gtin, _) in gtins_and_codes {
                let expected_length = match kind {
                    GtinKind::Gtin12 => 12,
                    GtinKind::Gtin8 => 8,
                    GtinKind::Gtin13 => 13,
                    GtinKind::Gtin14 => 14,
                };
                assert_eq!(
                    &gtin.to_string()[14 - expected_length..],
                    &gtin.to_string_no_padding()
                );
                assert_eq!(gtin.to_string_no_padding().len(), expected_length);
            }
        }
    }

    #[test]
    fn test_display_gtin() {
        let samples = sample_gtins();
        for (_kind, gtins_and_codes) in samples {
            for (gtin, _code) in gtins_and_codes {
                assert_eq!(
                    gtin.to_string(),
                    gtin.as_arr()
                        .iter()
                        .map(|d| d.to_string())
                        .collect::<String>()
                );
            }
        }
    }

    #[test]
    fn test_from_str_gtin() {
        let samples = sample_gtins();
        for (_kind, gtins_and_codes) in samples {
            for (gtin, code) in gtins_and_codes {
                assert_eq!(Gtin::from_str(&code).unwrap(), gtin);
            }
        }
    }

    #[test]
    fn test_serialize_gtin() {
        let samples = sample_gtins();
        for (_kind, gtins_and_codes) in samples {
            for (gtin, _code) in gtins_and_codes {
                let json = serde_json::json!({
                    "barcode": gtin,
                });
                let code = gtin.to_string();
                assert_eq!(json.to_string(), format!("{{\"barcode\":\"{}\"}}", code));
            }
        }
    }

    #[derive(Deserialize, PartialEq, Eq, Debug)]
    struct TestContainer {
        barcode: Gtin,
    }

    #[test]
    fn test_deserialize_gtin() {
        let samples = sample_gtins();
        for (_kind, gtins_and_codes) in samples {
            for (gtin, _code) in gtins_and_codes {
                let json = serde_json::json!({"barcode": gtin});
                let container: TestContainer = serde_json::from_value(json).unwrap();
                assert_eq!(container, TestContainer { barcode: gtin });
            }
        }
    }
}
