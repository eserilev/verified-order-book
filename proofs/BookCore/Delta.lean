import BookCore.Set

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- Given a valid side, the quantity at any price is 0 or more. -/
theorem ValidSide.quantityAt_nonneg {side : Side} {l : List Level} (hv : ValidSide side l)
    (x : Int) : 0 ≤ quantityAt l x := by
  unfold quantityAt
  split
  · rename_i y hy
    have := (hv.2 y (List.mem_of_find?_eq_some hy)).2
    omega
  · omega

/-- Rust's `i64::MAX` is the largest `I64` value. -/
theorem I64_MAX_val : core.num.I64.MAX.val = I64.max := by
  simp [core.num.I64.MAX, I64.rMax, I64.max, I64.numBits]

/-- Given a valid book, `get` returns the quantity at `price`, or 0 if there is no level at
    `price`. -/
theorem Book.get_spec (b : Book) (side : Side) (price : Std.I64) (hb : b.Valid) :
    b.get side price ⦃ q => q.val = quantityAt (levels b side) price.val ⦄ := by
  unfold Book.get
  cases side
  · have hv := hb.1
    simp only [levels] at hv ⊢
    step with lookup_spec as ⟨ lk, hlk ⟩
    · simpa [alloc.vec.Vec.deref] using hv.1
    simp only [alloc.vec.Vec.deref, Slice.from_val] at hlk
    cases lk with
    | Found i =>
      obtain ⟨hi, hpi⟩ := hlk
      step as ⟨ l1, hl1 ⟩
      have := hv.1.quantityAt_found hi
      rw [hpi] at this
      simp_all
    | InsertAt i =>
      obtain ⟨_, hbef, haft⟩ := hlk
      simp [quantityAt_insert_pos hbef haft]
  · have hv := hb.2
    simp only [levels] at hv ⊢
    step with lookup_spec as ⟨ lk, hlk ⟩
    · simpa [alloc.vec.Vec.deref] using hv.1
    simp only [alloc.vec.Vec.deref, Slice.from_val] at hlk
    cases lk with
    | Found i =>
      obtain ⟨hi, hpi⟩ := hlk
      step as ⟨ l1, hl1 ⟩
      have := hv.1.quantityAt_found hi
      rw [hpi] at this
      simp_all
    | InsertAt i =>
      obtain ⟨_, hbef, haft⟩ := hlk
      simp [quantityAt_insert_pos hbef haft]

/-- `apply_delta` adds `delta` to the quantity at `price`. A bad price, an overflow, or a
    result below 0 returns an error and leaves the book unchanged. Otherwise the book stays
    valid, the other side is untouched, and it returns `None` when the book did not change. -/
theorem Book.apply_delta_spec (b : Book) (side : Side) (price delta : Std.I64) (hb : b.Valid) :
    b.apply_delta side price delta ⦃ r b' =>
      if ValidPrice price.val then
        if quantityAt (levels b side) price.val + delta.val > I64.max then
          r = .Err .Overflow ∧ b' = b
        else if quantityAt (levels b side) price.val + delta.val < 0 then
          r = .Err .NegativeQuantity ∧ b' = b
        else
          b'.Valid ∧
          (∀ x, quantityAt (levels b' side) x =
            if x = price.val then quantityAt (levels b side) price.val + delta.val
            else quantityAt (levels b side) x) ∧
          (∀ s, s ≠ side → levels b' s = levels b s) ∧
          ∃ q : Std.I64, q.val = quantityAt (levels b side) price.val + delta.val ∧
            r = .Ok (if delta.val = 0 then none else some { side, level := { price, quantity := q } })
      else r = .Err .PriceOutOfRange ∧ b' = b ⦄ := by
  unfold Book.apply_delta
  step with valid_price_spec as ⟨ ok, hok ⟩
  split
  · have hvp : ValidPrice price.val := by simp_all
    simp only [hvp, ite_true]
    step with Book.get_spec as ⟨ current, hcur ⟩
    have hnn : 0 ≤ current.val := by
      rw [hcur]
      cases side
      · exact hb.1.quantityAt_nonneg _
      · exact hb.2.quantityAt_nonneg _
    rw [← hcur]
    have finish : ∀ quantity : Std.I64, quantity.val = current.val + delta.val →
        ¬ current.val + delta.val > I64.max → ¬ quantity < 0#i64 →
        (b.set side { price, quantity }) ⦃ r b' =>
          if current.val + delta.val > I64.max then r = .Err .Overflow ∧ b' = b
          else if current.val + delta.val < 0 then r = .Err .NegativeQuantity ∧ b' = b
          else
            b'.Valid ∧
            (∀ x, quantityAt (levels b' side) x =
              if x = price.val then current.val + delta.val else quantityAt (levels b side) x) ∧
            (∀ s, s ≠ side → levels b' s = levels b s) ∧
            ∃ q : Std.I64, q.val = current.val + delta.val ∧
              r = .Ok (if delta.val = 0 then none
                else some { side, level := { price, quantity := q } }) ⦄ := by
      intro quantity hq hno hneg
      have hneg' : ¬ quantity.val < 0 := by scalar_tac
      apply WP.spec_mono (Book.set_spec b side { price, quantity } hb)
      rintro ⟨r, b'⟩ h
      simp only [hvp, ite_true, hneg', ite_false] at h
      obtain ⟨hv', hq', hs', hr⟩ := h
      have hneg2 : ¬ current.val + delta.val < 0 := by omega
      simp only [hno, hneg2, ite_false]
      refine ⟨hv', ?_, hs', quantity, hq, ?_⟩
      · intro x; rw [hq' x, hq]
      · rw [hr, ← hcur, hq]
        by_cases hd : delta.val = 0 <;> simp [hd]
    split
    · have hmax := I64_MAX_val
      have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
      step as ⟨ i, hi ⟩
      split
      · have : current.val + delta.val > I64.max := by scalar_tac
        simp_all
      · step as ⟨ quantity, hq ⟩
        split
        · have : ¬ current.val + delta.val > I64.max := by scalar_tac
          have : current.val + delta.val < 0 := by scalar_tac
          simp_all
        · exact finish quantity hq (by scalar_tac) ‹_›
    · step as ⟨ quantity, hq ⟩
      split
      · have : ¬ current.val + delta.val > I64.max := by scalar_tac
        have : current.val + delta.val < 0 := by scalar_tac
        simp_all
      · exact finish quantity hq (by scalar_tac) ‹_›
  · simp_all

end book_core.Spec
