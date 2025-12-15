# gtin

Provides a data type and validator for working with Global Trade Identification Numbers (GTIN). Works with subsets like GTIN-8 (EAN8), GTIN-12 (UPC), GTIN-13 (EAN13), and GTIN-14.

This crate is intended to be simple and lightweight compared to other barcoding crates. For extra functionality like generating barcode images see [barcoders](https://github.com/buntine/barcoders).

# Examples

```rust
use gtin::{Gtin, GtinError};

fn main() {
    let sample = Gtin::from_str("0010576000465").unwrap();
    assert_eq!(sample.to_string(), "00010576000465".to_string());
    
    // 12 digit codes are assumed to be GTIN-12, and 2 leading zeros are inserted at the start for padding
    let upca_sample = Gtin::from_str("010576000465").unwrap();
    assert_eq!(upca_sample.to_string(), "00010576000465".to_string());

    // Attempting to create an invalid GTIN will cause an error
    assert_eq!(Gtin::from_str("010576000466"), Err(GtinError::InvalidCheckDigit));
}
```

