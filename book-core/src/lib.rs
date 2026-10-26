//! Pure L2 orderbook logic, kept within the subset of Rust that Aeneas can
//! translate to Lean.

/// Fixed-point denominator for prices and quantities: `SCALE` = $1 = 1 contract.
pub const SCALE: i64 = 1_000_000;

/// The two sides of an order book.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Buy,
    Sell,
}

/// A price in `SCALE` units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Price(pub i64);

/// A quantity in `SCALE` units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quantity(pub i64);

impl Price {
    /// Parses a decimal price like `"0.48"`.
    pub fn parse(s: &[u8]) -> Result<Price, Error> {
        match parse_fixed(s) {
            Ok(v) => Ok(Price(v)),
            Err(e) => Err(e),
        }
    }
}

impl Quantity {
    /// Parses a decimal quantity like `"125.5"`.
    pub fn parse(s: &[u8]) -> Result<Quantity, Error> {
        match parse_fixed(s) {
            Ok(v) => Ok(Quantity(v)),
            Err(e) => Err(e),
        }
    }
}

/// The price and the total quantity at that price in the order book.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Level {
    pub price: Price,
    pub quantity: Quantity,
}

/// The result of an update to the order book.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Update {
    pub side: Side,
    pub level: Level,
}

/// Why an order book operation was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A quantity update would reduce quantity below 0.
    NegativeQuantity,
    /// A delta would push a quantity past `i64::MAX`.
    Overflow,
    /// A price is not strictly between 0 and `SCALE`.
    PriceOutOfRange,
    /// A snapshot lists the same price twice on one side.
    DuplicatePrice,
    /// A decimal string could not be parsed into fixed point.
    BadDecimal,
}

/// The order book for a market.
/// - bids: sorted by highest price first.
/// - asks: sorted by lowest price first.
/// - each price appears at most once in each list.
/// - price is between 0 and `SCALE`, exclusive.
/// - every quantity is above 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Book {
    bids: Vec<Level>,
    asks: Vec<Level>,
}

impl Book {
    #[allow(clippy::new_without_default)] // derived Default becomes an Aeneas axiom
    pub fn new() -> Self {
        Book {
            bids: Vec::new(),
            asks: Vec::new(),
        }
    }

    pub fn bids(&self) -> &[Level] {
        &self.bids
    }

    pub fn asks(&self) -> &[Level] {
        &self.asks
    }

    /// Returns the quantity at `price`, or 0 if there is no level at `price`.
    pub fn get(&self, side: Side, price: Price) -> Quantity {
        let levels = match side {
            Side::Buy => &self.bids,
            Side::Sell => &self.asks,
        };
        match lookup(levels, side, price) {
            Lookup::Found(i) => levels[i].quantity,
            Lookup::InsertAt(_) => Quantity(0),
        }
    }

    /// Sets the absolute quantity at `level.price`. A `level.quantity` of 0
    /// removes the level. Returns `None` when the book did not change.
    pub fn set(&mut self, side: Side, level: Level) -> Result<Option<Update>, Error> {
        if !valid_price(level.price) {
            return Err(Error::PriceOutOfRange);
        }
        if level.quantity.0 < 0 {
            return Err(Error::NegativeQuantity);
        }
        let levels = match side {
            Side::Buy => &mut self.bids,
            Side::Sell => &mut self.asks,
        };
        match lookup(levels, side, level.price) {
            Lookup::Found(i) => {
                if levels[i].quantity.0 == level.quantity.0 {
                    return Ok(None);
                }
                if level.quantity.0 == 0 {
                    levels.remove(i);
                } else {
                    levels[i].quantity = level.quantity;
                }
            }
            Lookup::InsertAt(i) => {
                if level.quantity.0 == 0 {
                    return Ok(None);
                }
                levels.insert(i, level);
            }
        }
        Ok(Some(Update { side, level }))
    }

    /// Adds `delta` to the quantity at `price`. Returns `None` when the book did not change.
    pub fn apply_delta(
        &mut self,
        side: Side,
        price: Price,
        delta: i64,
    ) -> Result<Option<Update>, Error> {
        if !valid_price(price) {
            return Err(Error::PriceOutOfRange);
        }
        let current = self.get(side, price).0;
        if delta > 0 && current > i64::MAX - delta {
            return Err(Error::Overflow);
        }
        let quantity = current + delta;
        if quantity < 0 {
            return Err(Error::NegativeQuantity);
        }
        self.set(
            side,
            Level {
                price,
                quantity: Quantity(quantity),
            },
        )
    }

    /// Builds a book from a snapshot. Levels can be in any order, and levels with a
    /// quantity of 0 are skipped.
    pub fn from_levels(bids: &[Level], asks: &[Level]) -> Result<Book, Error> {
        let mut book = Book::new();
        book.add_levels(Side::Buy, bids)?;
        book.add_levels(Side::Sell, asks)?;
        Ok(book)
    }

    /// Sets each level on `side`. A price that is already on `side` is a `DuplicatePrice`.
    fn add_levels(&mut self, side: Side, levels: &[Level]) -> Result<(), Error> {
        let mut i = 0;
        while i < levels.len() {
            let level = levels[i];
            if self.get(side, level.price).0 != 0 {
                return Err(Error::DuplicatePrice);
            }
            self.set(side, level)?;
            i += 1;
        }
        Ok(())
    }
}

/// Returns `true` if price is between 0 and `SCALE`, exclusive.
fn valid_price(price: Price) -> bool {
    price.0 > 0 && price.0 < SCALE
}

/// Whether `p` is worse than `than` on `side` (lower for bids, higher for asks).
fn is_worse(side: Side, p: Price, than: Price) -> bool {
    match side {
        Side::Buy => p.0 < than.0,
        Side::Sell => p.0 > than.0,
    }
}

/// Parses a decimal string like `"0.48"` into fixed point. Fails instead of rounding when
/// a non-zero digit is past the 6th decimal place.
fn parse_fixed(s: &[u8]) -> Result<i64, Error> {
    let (value, decimals) = parse_digits(s)?;
    scale_up(value, decimals)
}

/// What `parse_digits` has read so far.
#[derive(Clone, Copy)]
struct Digits {
    /// The digits read so far as one integer, ignoring the dot.
    value: i64,
    /// How many of those digits came after the dot (at most 6).
    decimals: u32,
    any_digit: bool,
    seen_dot: bool,
}

/// Reads the digits of `s` as one integer, ignoring the dot. Returns the integer and how
/// many of its digits came after the dot (at most 6).
fn parse_digits(s: &[u8]) -> Result<(i64, u32), Error> {
    let mut d = Digits {
        value: 0,
        decimals: 0,
        any_digit: false,
        seen_dot: false,
    };
    let mut i = 0;
    while i < s.len() {
        d = read_char(d, s[i])?;
        i += 1;
    }
    if !d.any_digit {
        return Err(Error::BadDecimal);
    }
    Ok((d.value, d.decimals))
}

/// Reads one character of a decimal string.
fn read_char(d: Digits, c: u8) -> Result<Digits, Error> {
    if c == b'.' {
        if d.seen_dot {
            return Err(Error::BadDecimal);
        }
        return Ok(Digits {
            seen_dot: true,
            ..d
        });
    }
    if !c.is_ascii_digit() {
        return Err(Error::BadDecimal);
    }
    let digit = (c - b'0') as i64;
    if d.seen_dot && d.decimals == 6 {
        if digit != 0 {
            return Err(Error::BadDecimal);
        }
        return Ok(Digits {
            any_digit: true,
            ..d
        });
    }
    if d.value > (i64::MAX - digit) / 10 {
        return Err(Error::Overflow);
    }
    let decimals = if d.seen_dot {
        d.decimals + 1
    } else {
        d.decimals
    };
    Ok(Digits {
        value: d.value * 10 + digit,
        decimals,
        any_digit: true,
        seen_dot: d.seen_dot,
    })
}

/// Multiplies `value` by 10 until it has 6 decimal places.
fn scale_up(value: i64, decimals: u32) -> Result<i64, Error> {
    let mut value = value;
    let mut decimals = decimals;
    while decimals < 6 {
        if value > i64::MAX / 10 {
            return Err(Error::Overflow);
        }
        value *= 10;
        decimals += 1;
    }
    Ok(value)
}

/// Result of searching a side for a price.
enum Lookup {
    /// `price` is at this index.
    Found(usize),
    /// `price` is absent and belongs at this index.
    InsertAt(usize),
}

/// Finds the position of `price` in `levels`, or where it should be inserted.
fn lookup(levels: &[Level], side: Side, price: Price) -> Lookup {
    let mut i = 0;
    while i < levels.len() {
        let p = levels[i].price;
        if p.0 == price.0 {
            return Lookup::Found(i);
        }
        if is_worse(side, p, price) {
            return Lookup::InsertAt(i);
        }
        i += 1;
    }
    Lookup::InsertAt(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn level(price: i64, quantity: i64) -> Level {
        Level {
            price: Price(price),
            quantity: Quantity(quantity),
        }
    }

    #[test]
    fn set_get_keeps_sides_sorted() {
        let mut book = Book::new();

        // Inserted out of order. Each side must come back sorted.
        for price in [400_000, 600_000, 500_000] {
            book.set(Side::Buy, level(price, 10)).unwrap();
            book.set(Side::Sell, level(price, 10)).unwrap();
        }
        let bids: Vec<i64> = book.bids().iter().map(|l| l.price.0).collect();
        let asks: Vec<i64> = book.asks().iter().map(|l| l.price.0).collect();
        assert_eq!(bids, [600_000, 500_000, 400_000]);
        assert_eq!(asks, [400_000, 500_000, 600_000]);

        // Same quantity, or removing a missing level, changes nothing.
        assert_eq!(book.set(Side::Buy, level(500_000, 10)), Ok(None));
        assert_eq!(book.set(Side::Buy, level(700_000, 0)), Ok(None));

        // Quantity 0 removes the level and reports it.
        assert_eq!(
            book.set(Side::Buy, level(500_000, 0))
                .unwrap()
                .unwrap()
                .level
                .quantity,
            Quantity(0)
        );
        assert_eq!(book.get(Side::Buy, Price(500_000)), Quantity(0));
        assert_eq!(book.bids().len(), 2);

        // Price must be strictly between 0 and `SCALE`, and quantity not negative.
        assert_eq!(
            book.set(Side::Buy, level(0, 1)),
            Err(Error::PriceOutOfRange)
        );
        assert_eq!(
            book.set(Side::Buy, level(SCALE, 1)),
            Err(Error::PriceOutOfRange)
        );
        assert_eq!(
            book.set(Side::Buy, level(1, -1)),
            Err(Error::NegativeQuantity)
        );
    }

    #[test]
    fn apply_delta_tracks_absolute_quantity() {
        let mut book = Book::new();

        // Deltas accumulate. Updates contain the new total.
        book.apply_delta(Side::Buy, Price(500_000), 10).unwrap();
        let update = book
            .apply_delta(Side::Buy, Price(500_000), 5)
            .unwrap()
            .unwrap();
        assert_eq!(update.level.quantity, Quantity(15));

        // Zero delta changes nothing.
        assert_eq!(book.apply_delta(Side::Buy, Price(500_000), 0), Ok(None));

        // Reducing to zero removes the level.
        book.apply_delta(Side::Buy, Price(500_000), -15).unwrap();
        assert!(book.bids().is_empty());

        // Going below zero is rejected.
        assert_eq!(
            book.apply_delta(Side::Buy, Price(500_000), -1),
            Err(Error::NegativeQuantity)
        );
        assert_eq!(
            book.apply_delta(Side::Buy, Price(500_000), i64::MIN),
            Err(Error::NegativeQuantity)
        );

        // Overflow is rejected and leaves the level untouched.
        book.apply_delta(Side::Sell, Price(500_000), i64::MAX)
            .unwrap();
        assert_eq!(
            book.apply_delta(Side::Sell, Price(500_000), 1),
            Err(Error::Overflow)
        );
        assert_eq!(book.get(Side::Sell, Price(500_000)), Quantity(i64::MAX));

        // A bad price is rejected regardless of delta.
        for delta in [-1, 0, 1] {
            assert_eq!(
                book.apply_delta(Side::Buy, Price(0), delta),
                Err(Error::PriceOutOfRange)
            );
            assert_eq!(
                book.apply_delta(Side::Buy, Price(SCALE), delta),
                Err(Error::PriceOutOfRange)
            );
        }
    }

    #[test]
    fn errors_leave_book_unchanged() {
        let mut book = Book::new();
        book.set(Side::Buy, level(400_000, 10)).unwrap();
        book.set(Side::Sell, level(600_000, i64::MAX)).unwrap();
        let before = book.clone();

        assert!(book.set(Side::Buy, level(0, 1)).is_err());
        assert!(book.set(Side::Buy, level(400_000, -1)).is_err());
        assert!(book.apply_delta(Side::Buy, Price(SCALE), 1).is_err());
        assert!(book.apply_delta(Side::Buy, Price(400_000), -11).is_err());
        assert!(book.apply_delta(Side::Sell, Price(600_000), 1).is_err());

        assert_eq!(book, before);
    }

    #[test]
    fn from_levels_sorts_and_validates() {
        let book = Book::from_levels(
            &[level(400_000, 1), level(600_000, 2), level(500_000, 0)],
            &[level(700_000, 3), level(650_000, 4)],
        )
        .unwrap();
        assert_eq!(book.bids(), [level(600_000, 2), level(400_000, 1)]);
        assert_eq!(book.asks(), [level(650_000, 4), level(700_000, 3)]);

        let dup = [level(400_000, 1), level(400_000, 2)];
        assert_eq!(Book::from_levels(&dup, &[]), Err(Error::DuplicatePrice));
        assert_eq!(
            Book::from_levels(&[], &[level(0, 1)]),
            Err(Error::PriceOutOfRange)
        );
        assert_eq!(
            Book::from_levels(&[level(1, -1)], &[]),
            Err(Error::NegativeQuantity)
        );
    }

    #[test]
    fn parse_fixed_is_exact() {
        assert_eq!(parse_fixed(b"0.48"), Ok(480_000));
        assert_eq!(parse_fixed(b"125.5"), Ok(125_500_000));
        assert_eq!(parse_fixed(b"7"), Ok(7_000_000));
        assert_eq!(parse_fixed(b".5"), Ok(500_000));
        assert_eq!(parse_fixed(b"5."), Ok(5_000_000));
        assert_eq!(parse_fixed(b"0.000001"), Ok(1));
        assert_eq!(parse_fixed(b"0.48000000"), Ok(480_000));

        // Would lose precision.
        assert_eq!(parse_fixed(b"0.0000001"), Err(Error::BadDecimal));
        // Malformed.
        for bad in [
            &b""[..],
            b".",
            b"1.2.3",
            b"-1",
            b"+1",
            b"1e3",
            b" 1",
            b"0,5",
        ] {
            assert_eq!(parse_fixed(bad), Err(Error::BadDecimal), "{bad:?}");
        }
        // Largest value that fits, then one past it.
        assert_eq!(parse_fixed(b"9223372036854.775807"), Ok(i64::MAX));
        assert_eq!(parse_fixed(b"9223372036854.775808"), Err(Error::Overflow));
        assert_eq!(parse_fixed(b"9223372036855"), Err(Error::Overflow));
    }
}
