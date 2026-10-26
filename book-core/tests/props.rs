//! Checks `Book` against a `BTreeMap` reference model over random operation
//! sequences.

use std::collections::BTreeMap;

use book_core::{Book, Error, Level, Price, Quantity, SCALE, Side, Update};
use proptest::prelude::*;

fn level(price: i64, quantity: i64) -> Level {
    Level {
        price: Price(price),
        quantity: Quantity(quantity),
    }
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Set(Side, i64, i64),
    Delta(Side, i64, i64),
}

#[derive(Default)]
struct Model {
    bids: BTreeMap<i64, i64>,
    asks: BTreeMap<i64, i64>,
}

impl Model {
    fn side(&mut self, side: Side) -> &mut BTreeMap<i64, i64> {
        match side {
            Side::Buy => &mut self.bids,
            Side::Sell => &mut self.asks,
        }
    }

    fn set(&mut self, side: Side, price: i64, quantity: i64) -> Result<Option<Update>, Error> {
        if price <= 0 || price >= SCALE {
            return Err(Error::PriceOutOfRange);
        }
        if quantity < 0 {
            return Err(Error::NegativeQuantity);
        }
        let levels = self.side(side);
        let current = levels.get(&price).copied().unwrap_or(0);
        if current == quantity {
            return Ok(None);
        }
        if quantity == 0 {
            levels.remove(&price);
        } else {
            levels.insert(price, quantity);
        }
        Ok(Some(Update {
            side,
            level: level(price, quantity),
        }))
    }

    fn apply_delta(&mut self, side: Side, price: i64, delta: i64) -> Result<Option<Update>, Error> {
        if price <= 0 || price >= SCALE {
            return Err(Error::PriceOutOfRange);
        }
        let current = self.side(side).get(&price).copied().unwrap_or(0);
        let quantity = current.checked_add(delta).ok_or(Error::Overflow)?;
        if quantity < 0 {
            return Err(Error::NegativeQuantity);
        }
        self.set(side, price, quantity)
    }

    fn bids(&self) -> Vec<Level> {
        self.bids
            .iter()
            .rev()
            .map(|(&price, &quantity)| level(price, quantity))
            .collect()
    }

    fn asks(&self) -> Vec<Level> {
        self.asks
            .iter()
            .map(|(&price, &quantity)| level(price, quantity))
            .collect()
    }
}

fn side() -> impl Strategy<Value = Side> {
    prop_oneof![Just(Side::Buy), Just(Side::Sell)]
}

// Few distinct prices so operations keep hitting the same levels, plus the
// edges of the valid range.
fn price() -> impl Strategy<Value = i64> {
    prop_oneof![
        prop::sample::select(vec![-1, 0, 1, SCALE - 1, SCALE, SCALE + 1]),
        (1..10i64).prop_map(|n| n * 100_000),
    ]
}

fn quantity() -> impl Strategy<Value = i64> {
    prop_oneof![
        8 => 0..20i64,
        1 => prop::sample::select(vec![-1, i64::MIN, i64::MAX, i64::MAX - 1]),
    ]
}

fn delta() -> impl Strategy<Value = i64> {
    prop_oneof![
        8 => -20..20i64,
        1 => prop::sample::select(vec![i64::MIN, i64::MAX, i64::MIN + 1, i64::MAX - 1]),
    ]
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        (side(), price(), quantity()).prop_map(|(s, p, q)| Op::Set(s, p, q)),
        (side(), price(), delta()).prop_map(|(s, p, d)| Op::Delta(s, p, d)),
    ]
}

fn assert_invariants(levels: &[Level], descending: bool) {
    for l in levels {
        assert!(l.price.0 > 0 && l.price.0 < SCALE, "bad price {l:?}");
        assert!(l.quantity.0 > 0, "non-positive quantity {l:?}");
    }
    for pair in levels.windows(2) {
        let sorted = if descending {
            pair[0].price.0 > pair[1].price.0
        } else {
            pair[0].price.0 < pair[1].price.0
        };
        assert!(sorted, "not strictly sorted: {pair:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2_000))]

    #[test]
    fn book_matches_model(ops in prop::collection::vec(op(), 0..200)) {
        let mut book = Book::new();
        let mut model = Model::default();
        let mut updates = Vec::new();

        for op in ops {
            let (got, want) = match op {
                Op::Set(s, p, q) => (book.set(s, level(p, q)), model.set(s, p, q)),
                Op::Delta(s, p, d) => (book.apply_delta(s, Price(p), d), model.apply_delta(s, p, d)),
            };
            prop_assert_eq!(got, want, "op {:?}", op);
            prop_assert_eq!(book.bids().to_vec(), model.bids());
            prop_assert_eq!(book.asks().to_vec(), model.asks());
            assert_invariants(book.bids(), true);
            assert_invariants(book.asks(), false);
            if let Ok(Some(u)) = got {
                updates.push(u);
            }
        }

        // Replaying the emitted updates must rebuild the same book.
        let mut replayed = Book::new();
        for u in updates {
            replayed.set(u.side, u.level).unwrap();
        }
        prop_assert_eq!(replayed, book);
    }
}

proptest! {
    #[test]
    fn parse_fixed_round_trips(value in 0..=i64::MAX, trim in any::<bool>(), extra_zeros in 0..4usize) {
        let mut text = format!("{}.{:06}", value / SCALE, value % SCALE);
        if trim {
            text = text.trim_end_matches('0').to_string();
        }
        text.push_str(&"0".repeat(extra_zeros));
        prop_assert_eq!(Quantity::parse(text.as_bytes()), Ok(Quantity(value)), "{}", text);
    }
}
