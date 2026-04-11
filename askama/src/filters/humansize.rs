use core::convert::Infallible;
use core::fmt;

use crate::{FastWritable, NO_VALUES, Values};

/// Returns adequate string representation (in KB, ..) of number of bytes
///
/// ## Example
/// ```
/// # use askama::Template;
/// #[derive(Template)]
/// #[template(
///     source = "Filesize: {{ size_in_bytes | filesizeformat }}.",
///     ext = "html"
/// )]
/// struct Example {
///     size_in_bytes: u64,
/// }
///
/// let tmpl = Example { size_in_bytes: 1_234_567 };
/// assert_eq!(tmpl.to_string(),  "Filesize: 1.23 MB.");
/// ```
#[inline]
pub fn filesizeformat(bytes: u128, precision: u8) -> Result<FilesizeFormatFilter, Infallible> {
    Ok(FilesizeFormatFilter { bytes, precision })
}

#[derive(Debug, Clone, Copy)]
pub struct FilesizeFormatFilter {
    /// The number of bytes to format nicely
    bytes: u128,
    /// The precision with which to display the generated string.
    /// This determines the number of digits after the decimal separator.
    precision: u8,
}

impl fmt::Display for FilesizeFormatFilter {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(self.write_into(f, NO_VALUES)?)
    }
}

impl FastWritable for FilesizeFormatFilter {
    fn write_into(&self, dest: &mut dyn fmt::Write, values: &dyn Values) -> crate::Result<()> {
        if self.bytes < 1000 {
            (self.bytes as u32).write_into(dest, values)?;
            return Ok(dest.write_str(" B")?);
        }

        // find appropriate unit to format in
        let unit = SI_PREFIXES
            .iter()
            .take_while(|siprefix| siprefix.lower_bound <= self.bytes)
            .last()
            .unwrap_or(&SI_PREFIXES[SI_PREFIXES.len() - 1]);
        // divide number up into "full" units, and remainder
        let integer = self.bytes / unit.lower_bound;
        let remainder = self.bytes % unit.lower_bound;

        // Compute fractional part with desired precision
        // limit precision to the chosen unit's exponent - a greater precision will just
        // generated tailing 0s that will be dropped.
        let precision = self.precision.min(unit.exponent);

        // integer portion (before decimal point)
        integer.write_into(dest, values)?;
        if precision > 0 {
            let mut scale = 10u128.pow(precision as u32);
            let mut fractional = remainder.saturating_mul(scale) / unit.lower_bound;
            if fractional > 0 {
                '.'.write_into(dest, values)?;
                for _ in 0..precision {
                    scale /= 10;
                    let digit = (b'0' + (fractional / scale) as u8) as char;
                    digit.write_into(dest, values)?;
                    fractional %= scale;
                    if fractional == 0 {
                        break;
                    }
                }
            }
        }
        ' '.write_into(dest, values)?;
        unit.prefix_char.write_into(dest, values)?;
        'B'.write_into(dest, values)?;

        Ok(())
    }
}

struct SiPrefix {
    /// SI-prefix character that is prepended to the unit (B) as scaler.
    prefix_char: char,
    /// The smallest number of bytes that will be represented using this si-prefix.
    /// This is 10 ^ self.exponent
    lower_bound: u128,
    /// The exponent (10 ^ exponent) that calculates this si-prefix's lower bound.
    exponent: u8,
}
impl SiPrefix {
    const fn new(prefix_char: char, exponent: u8) -> Self {
        Self {
            prefix_char,
            lower_bound: 10u128.pow(exponent as u32),
            exponent,
        }
    }
}

/// The set of supported SI-Prefixes.
/// The fitting prefix for a given number of bytes is selected by choosing the prefix with
/// the highest lower_bound, that is lower than the number of bytes.
const SI_PREFIXES: &[SiPrefix] = &[
    SiPrefix::new('k', 3),
    SiPrefix::new('M', 6),
    SiPrefix::new('G', 9),
    SiPrefix::new('T', 12),
    SiPrefix::new('P', 15),
    SiPrefix::new('E', 18),
    SiPrefix::new('Z', 21),
    SiPrefix::new('Y', 24),
    SiPrefix::new('R', 27),
    SiPrefix::new('Q', 30),
];

#[test]
#[cfg(feature = "alloc")]
fn test_filesizeformat_edgecases() {
    use alloc::string::ToString;

    assert_eq!(filesizeformat(1000, 0).unwrap().to_string(), "1 kB");

    assert_eq!(
        filesizeformat(954_548_589_125_249_215_468, 0)
            .unwrap()
            .to_string(),
        "954 EB"
    );
    assert_eq!(
        filesizeformat(954_548_589_125_249_215_468, 10)
            .unwrap()
            .to_string(),
        "954.5485891252 EB"
    );
    assert_eq!(
        filesizeformat(954_548_589_125_249_215_468, 255)
            .unwrap()
            .to_string(),
        "954.548589125249215468 EB"
    );
}

#[test]
#[cfg(feature = "alloc")]
fn test_filesizeformat_prec2() {
    use alloc::string::ToString;

    assert_eq!(filesizeformat(0, 2).unwrap().to_string(), "0 B");
    assert_eq!(filesizeformat(999, 2).unwrap().to_string(), "999 B");
    assert_eq!(filesizeformat(1000, 2).unwrap().to_string(), "1 kB");
    assert_eq!(filesizeformat(1023, 2).unwrap().to_string(), "1.02 kB");
    assert_eq!(filesizeformat(1024, 2).unwrap().to_string(), "1.02 kB");
    assert_eq!(filesizeformat(1025, 2).unwrap().to_string(), "1.02 kB");
    assert_eq!(filesizeformat(1100, 2).unwrap().to_string(), "1.1 kB");
    assert_eq!(filesizeformat(9_499_014, 2).unwrap().to_string(), "9.49 MB");
    assert_eq!(
        filesizeformat(954_548_589, 2).unwrap().to_string(),
        "954.54 MB"
    );
    assert_eq!(
        filesizeformat(300_000_000_000, 2).unwrap().to_string(),
        "300 GB"
    );
    assert_eq!(
        filesizeformat(600_000_000_000, 2).unwrap().to_string(),
        "600 GB"
    );
    assert_eq!(
        filesizeformat(7_000_000_000_000, 2).unwrap().to_string(),
        "7 TB"
    );
    assert_eq!(
        filesizeformat(2_300_000_000_000_000, 2)
            .unwrap()
            .to_string(),
        "2.3 PB"
    );
    assert_eq!(
        filesizeformat(9_900_000_000_000_000_000, 2)
            .unwrap()
            .to_string(),
        "9.9 EB"
    );
    assert_eq!(
        filesizeformat(4_500_000_000_000_000_000_000, 2)
            .unwrap()
            .to_string(),
        "4.5 ZB"
    );
}

#[test]
#[cfg(feature = "alloc")]
fn test_filesizeformat_prec3() {
    use alloc::string::ToString;

    assert_eq!(filesizeformat(0, 3).unwrap().to_string(), "0 B");
    assert_eq!(filesizeformat(999, 3).unwrap().to_string(), "999 B");
    assert_eq!(filesizeformat(1000, 3).unwrap().to_string(), "1 kB");
    assert_eq!(filesizeformat(1023, 3).unwrap().to_string(), "1.023 kB");
    assert_eq!(filesizeformat(1024, 3).unwrap().to_string(), "1.024 kB");
    assert_eq!(filesizeformat(1025, 3).unwrap().to_string(), "1.025 kB");
    assert_eq!(filesizeformat(1100, 3).unwrap().to_string(), "1.1 kB");
    assert_eq!(
        filesizeformat(9_499_014, 3).unwrap().to_string(),
        "9.499 MB"
    );
    assert_eq!(
        filesizeformat(954_548_589, 3).unwrap().to_string(),
        "954.548 MB"
    );
    assert_eq!(
        filesizeformat(300_000_000_000, 3).unwrap().to_string(),
        "300 GB"
    );
    assert_eq!(
        filesizeformat(600_000_000_000, 3).unwrap().to_string(),
        "600 GB"
    );
    assert_eq!(
        filesizeformat(7_000_000_000_000, 3).unwrap().to_string(),
        "7 TB"
    );
    assert_eq!(
        filesizeformat(2_300_000_000_000_000, 3)
            .unwrap()
            .to_string(),
        "2.3 PB"
    );
    assert_eq!(
        filesizeformat(9_900_000_000_000_000_000, 3)
            .unwrap()
            .to_string(),
        "9.9 EB"
    );
    assert_eq!(
        filesizeformat(4_500_000_000_000_000_000_000, 3)
            .unwrap()
            .to_string(),
        "4.5 ZB"
    );
}
