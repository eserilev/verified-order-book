import BookCore.Funs

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- Whether `p` is worse than `than` on `side` (lower for bids, higher for asks). -/
def Worse : Side → Int → Int → Prop
  | .Buy, p, than => p < than
  | .Sell, p, than => p > than

/-- Lets `Worse` be checked with `decide`. -/
instance (side : Side) (p than : Int) : Decidable (Worse side p than) := by
  cases side <;> unfold Worse <;> infer_instance

/-- Levels are sorted best price first, and each price appears at most once. -/
def Sorted (side : Side) (l : List Level) : Prop :=
  l.Pairwise fun a b => Worse side b.price.val a.price.val

/-- Price is between 0 and `SCALE`, exclusive. -/
def ValidPrice (p : Int) : Prop := 0 < p ∧ p < SCALE.val

/-- Lets `ValidPrice` be checked with `decide`. -/
instance (p : Int) : Decidable (ValidPrice p) := by
  unfold ValidPrice; infer_instance

/-- A valid side of the order book. Levels are sorted, each price is between 0 and
    `SCALE` exclusive, and every quantity is above 0. -/
def ValidSide (side : Side) (l : List Level) : Prop :=
  Sorted side l ∧ ∀ x ∈ l, ValidPrice x.price.val ∧ 0 < x.quantity.val

/-- Returns the quantity at `p`, or 0 if there is no level at `p`. -/
def quantityAt (l : List Level) (p : Int) : Int :=
  match l.find? (fun x => x.price.val = p) with
  | some x => x.quantity.val
  | none => 0

/-- The levels on one side of the order book. -/
def levels (b : Book) : Side → List Level
  | .Buy => b.bids.val
  | .Sell => b.asks.val

/-- Both sides of the order book are valid. -/
def _root_.book_core.Book.Valid (b : Book) : Prop :=
  ValidSide .Buy (levels b .Buy) ∧ ValidSide .Sell (levels b .Sell)

/-- `SCALE` is 1,000,000. -/
theorem SCALE_val : SCALE.val = 1000000 := by
  unfold SCALE; rfl

/-- `is_worse` returns whether `p` is worse than `than` on `side`. -/
theorem is_worse_spec (side : Side) (p than : Std.I64) :
    is_worse side p than ⦃ r => r = decide (Worse side p.val than.val) ⦄ := by
  cases side <;> simp [is_worse, Worse]

/-- `valid_price` returns whether `price` is between 0 and `SCALE`, exclusive. -/
theorem valid_price_spec (price : Std.I64) :
    valid_price price ⦃ r => r = decide (ValidPrice price.val) ⦄ := by
  unfold valid_price ValidPrice
  split <;> simp_all

end book_core.Spec
