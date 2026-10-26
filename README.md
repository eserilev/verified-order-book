# verified-order-book

An L2 order book in Rust, with Lean proofs about the actual code. [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas) translate the Rust into Lean, and the proofs are written against that translation.

## What is proven

Each side of a valid book is sorted best price first: bids from high to low, asks from low to high. Because the order is strict, no price appears twice. Every price is above 0 and below `SCALE`, and every quantity is above 0 (`ValidSide` in `proofs/BookCore/Spec.lean`).

| Theorem | File | Says |
|---|---|---|
| `Book.set_spec` | `Set.lean` | `set` keeps the book valid and changes only the quantity at one price. A bad input returns an error and leaves the book unchanged. |
| `Book.apply_delta_spec` | `Delta.lean` | `apply_delta` adds the delta at one price. An overflow or a negative result returns an error and leaves the book unchanged. |
| `Book.get_spec` | `Delta.lean` | `get` returns the quantity at a price, or 0. |
| `run_replay` | `Replay.lean` | Applying the updates the book emits, starting from the initial book, rebuilds the final book. |
| `Quantity.parse_correct` | `Parse.lean` | Parsing succeeds exactly on decimal strings whose exact value fits in an `i64` at 6 decimal places, and returns that value. |

`book-core/tests/props.rs` also checks `Book` against a `BTreeMap` model with proptest.

## Build

Tests:

```sh
cd book-core && cargo test
```

Proofs need Aeneas at commit `74aabd52`, plus `aeneas-vec-insert.patch`. Upstream, the model of `Vec::insert` fails when inserting at the end of a vector, but Rust allows that.

```sh
git clone https://github.com/AeneasVerif/aeneas && cd aeneas
git checkout 74aabd52 && git apply ../verified-order-book/aeneas-vec-insert.patch
cd backends/lean && lake exe cache get && lake build
```

Then:

```sh
ln -s /path/to/aeneas/backends/lean proofs/.aeneas
cd proofs && lake build
```

`proofs/extract.sh` regenerates `Types.lean` and `Funs.lean` from the Rust. It needs a built Charon and Aeneas (`AENEAS_DIR`).
