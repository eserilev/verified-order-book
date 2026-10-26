import BookCore.Lookup
import Mathlib.Data.Int.Interval

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- If `a` is a worse price than `b`, then `a` and `b` are different prices. -/
theorem Worse.ne {side : Side} {a b : Int} (h : Worse side a b) : a ≠ b := by
  cases side <;> simp only [Worse] at h <;> omega

/-- Inserting `x` at index `i` gives the first `i` elements, then `x`, then the rest. -/
theorem insertIdx_eq_take_drop {α : Type _} (l : List α) (x : α) :
    ∀ i, i ≤ l.length → l.insertIdx i x = l.take i ++ x :: l.drop i := by
  induction l with
  | nil => intro i hi; simp at hi; subst hi; simp
  | cons y l ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i => simp [List.insertIdx_succ_cons, ih i (by simp at hi; omega)]

/-! ### `quantityAt` -/

/-- The quantity at `x` is the first level's quantity if its price is `x`, otherwise the
    quantity at `x` in the rest. -/
theorem quantityAt_cons (y : Level) (l : List Level) (x : Int) :
    quantityAt (y :: l) x = if y.price.val = x then y.quantity.val else quantityAt l x := by
  unfold quantityAt
  by_cases h : y.price.val = x <;> simp [h]

/-- If no level in `A` has price `x`, the quantity at `x` in `A` followed by `B` is the
    quantity at `x` in `B`. -/
theorem quantityAt_append_of_ne {A B : List Level} {x : Int} (h : ∀ y ∈ A, y.price.val ≠ x) :
    quantityAt (A ++ B) x = quantityAt B x := by
  induction A with
  | nil => simp
  | cons y A ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [List.cons_append, quantityAt_cons]
    simp [h.1, ih h.2]

/-- If no level has price `x`, the quantity at `x` is 0. -/
theorem quantityAt_eq_zero {l : List Level} {x : Int} (h : ∀ y ∈ l, y.price.val ≠ x) :
    quantityAt l x = 0 := by
  have := quantityAt_append_of_ne (B := []) h
  simpa [quantityAt] using this

/-- Removing a level whose price is not `x` does not change the quantity at `x`. -/
theorem quantityAt_skip (A B : List Level) {y : Level} {x : Int} (h : y.price.val ≠ x) :
    quantityAt (A ++ y :: B) x = quantityAt (A ++ B) x := by
  induction A with
  | nil => simp [quantityAt_cons, h]
  | cons z A ih => simp only [List.cons_append, quantityAt_cons, ih]

/-! ### Prices around a position -/

/-- Given a sorted side, no level before index `i` has the same price as the level at `i`. -/
theorem Sorted.ne_before {side : Side} {l : List Level} (hs : Sorted side l) {i : Nat}
    (hi : i < l.length) : ∀ y ∈ l.take i, y.price.val ≠ l[i].price.val := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hy
  exact (hs.later_is_worse (by omega) hi).ne.symm

/-- Given a sorted side, no level after index `i` has the same price as the level at `i`. -/
theorem Sorted.ne_after {side : Side} {l : List Level} (hs : Sorted side l) {i : Nat}
    (hi : i < l.length) : ∀ y ∈ l.drop (i + 1), y.price.val ≠ l[i].price.val := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hy
  have := (hs.later_is_worse (i := i) (by omega) hj).ne
  simpa [Nat.add_comm] using this

/-- Given a sorted side, the quantity at the price of the level at `i` is that level's
    quantity. -/
theorem Sorted.quantityAt_found {side : Side} {l : List Level} (hs : Sorted side l) {i : Nat}
    (hi : i < l.length) : quantityAt l l[i].price.val = l[i].quantity.val := by
  have hl : l.take i ++ l[i] :: l.drop (i + 1) = l := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have h := quantityAt_append_of_ne (B := l[i] :: l.drop (i + 1)) (hs.ne_before hi)
  rw [hl, quantityAt_cons, ite_eq_left rfl] at h
  exact h

/-- If every level before `i` has a better price than `p` and every level from `i` on has
    a worse one, the quantity at `p` is 0. -/
theorem quantityAt_insert_pos {side : Side} {l : List Level} {i : Nat} {p : Int}
    (hb : ∀ j (h : j < l.length), j < i → Worse side p l[j].price.val)
    (ha : ∀ j (h : j < l.length), i ≤ j → Worse side l[j].price.val p) :
    quantityAt l p = 0 := by
  apply quantityAt_eq_zero
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  rcases Nat.lt_or_ge j i with h | h
  · exact (hb j hj h).ne.symm
  · exact (ha j hj h).ne

/-- A valid side has fewer than `SCALE` levels, since its prices are distinct and between 0
    and `SCALE`. -/
theorem ValidSide.length_lt {side : Side} {l : List Level} (hv : ValidSide side l) :
    l.length < SCALE.val := by
  have hnd : (l.map (·.price.val)).Nodup := by
    have h := hv.1
    unfold Sorted at h
    rw [List.Nodup, List.pairwise_map]
    exact h.imp fun hw => (Worse.ne hw).symm
  have hsub : (l.map (·.price.val)).toFinset ⊆ Finset.Ioo 0 SCALE.val := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := (hv.2 y hy).1
    simp only [ValidPrice] at this
    simp [Finset.mem_Ioo, this]
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Int.card_Ioo, SCALE_val] at hcard
  rw [SCALE_val]
  omega

/-! ### The three ways `set` changes a side -/

/-- Inserting a valid level where `lookup` says it belongs keeps the side valid, and only
    changes the quantity at that level's price. -/
theorem ValidSide.insert {side : Side} {l : List Level} (hv : ValidSide side l) {i : Nat}
    (hi : i ≤ l.length) {lv : Level}
    (hb : ∀ j (h : j < l.length), j < i → Worse side lv.price.val l[j].price.val)
    (ha : ∀ j (h : j < l.length), i ≤ j → Worse side l[j].price.val lv.price.val)
    (hlv : ValidPrice lv.price.val ∧ 0 < lv.quantity.val) :
    ValidSide side (l.insertIdx i lv) ∧
    ∀ x, quantityAt (l.insertIdx i lv) x =
      if x = lv.price.val then lv.quantity.val else quantityAt l x := by
  rw [insertIdx_eq_take_drop l lv i hi]
  have take_ne : ∀ y ∈ l.take i, y.price.val ≠ lv.price.val := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hy
    exact (hb j (by omega) (by omega)).ne.symm
  have drop_worse : ∀ y ∈ l.drop i, Worse side y.price.val lv.price.val := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hy
    exact ha (i + j) (by omega) (by omega)
  have hsplit := hv.1
  unfold Sorted at hsplit
  rw [← List.take_append_drop i l, List.pairwise_append] at hsplit
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Sorted
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hsplit.1, ⟨drop_worse, hsplit.2.1⟩, ?_⟩
    intro a ha' b hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha'
      exact hb j (by omega) (by omega)
    · exact hsplit.2.2 a ha' b hb'
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hv.2 x (List.mem_of_mem_take hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hlv
      · exact hv.2 x (List.mem_of_mem_drop hx)
  · intro x
    by_cases hx : x = lv.price.val
    · subst hx
      rw [quantityAt_append_of_ne take_ne, quantityAt_cons, ite_eq_left rfl, ite_eq_left rfl]
    · rw [quantityAt_skip _ _ (Ne.symm hx), List.take_append_drop, ite_eq_right hx]

/-- Removing the level at `i` keeps the side valid, and only sets the quantity at its
    price to 0. -/
theorem ValidSide.erase {side : Side} {l : List Level} (hv : ValidSide side l) {i : Nat}
    (hi : i < l.length) :
    ValidSide side (l.eraseIdx i) ∧
    ∀ x, quantityAt (l.eraseIdx i) x = if x = l[i].price.val then 0 else quantityAt l x := by
  refine ⟨⟨hv.1.sublist (List.eraseIdx_sublist _ _),
    fun x hx => hv.2 x (List.mem_of_mem_eraseIdx hx)⟩, ?_⟩
  intro x
  have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  by_cases hx : x = l[i].price.val
  · subst hx
    rw [ite_eq_left rfl, quantityAt_append_of_ne (hv.1.ne_before hi),
      quantityAt_eq_zero (hv.1.ne_after hi)]
  · rw [ite_eq_right hx]
    conv => rhs; rw [hl]
    rw [quantityAt_skip _ _ (Ne.symm hx)]

/-- Replacing the level at `i` with one at the same price and a quantity above 0 keeps the
    side valid, and only changes the quantity at that price. -/
theorem ValidSide.update {side : Side} {l : List Level} (hv : ValidSide side l) {i : Nat}
    (hi : i < l.length) {lv : Level} (hp : lv.price = l[i].price) (hq : 0 < lv.quantity.val) :
    ValidSide side (l.set i lv) ∧
    ∀ x, quantityAt (l.set i lv) x =
      if x = lv.price.val then lv.quantity.val else quantityAt l x := by
  have hmap : (l.set i lv).map (·.price.val) = l.map (·.price.val) := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_set]
    split <;> simp_all
  have hsorted : Sorted side (l.set i lv) := by
    have h := hv.1
    unfold Sorted at h ⊢
    have h' : ((l.map (·.price.val)).Pairwise fun a b => Worse side b a) := by
      rw [List.pairwise_map]; exact h
    rw [← hmap] at h'
    rw [List.pairwise_map] at h'
    exact h'
  have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hset : l.set i lv = l.take i ++ lv :: l.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
  refine ⟨⟨hsorted, ?_⟩, ?_⟩
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hv.2 x hx
    · exact ⟨hp ▸ (hv.2 l[i] (List.getElem_mem hi)).1, hq⟩
  · intro x
    rw [hset]
    by_cases hx : x = lv.price.val
    · subst hx
      rw [ite_eq_left rfl, quantityAt_append_of_ne (by rw [hp]; exact hv.1.ne_before hi),
        quantityAt_cons, ite_eq_left rfl]
    · rw [ite_eq_right hx, quantityAt_skip _ _ (Ne.symm hx)]
      conv => rhs; rw [hl]
      rw [quantityAt_skip _ _ (by rw [← hp]; exact Ne.symm hx)]

/-- `set` sets the absolute quantity at `level.price`, and a `level.quantity` of 0 removes
    the level. A bad price or negative quantity returns an error and leaves the book
    unchanged. Otherwise the book stays valid, the other side is untouched, and it returns
    `None` when the book did not change. -/
theorem Book.set_spec (b : Book) (side : Side) (level : Level) (hb : b.Valid) :
    b.set side level ⦃ r b' =>
      if ValidPrice level.price.val then
        if level.quantity.val < 0 then r = .Err .NegativeQuantity ∧ b' = b
        else
          b'.Valid ∧
          (∀ x, quantityAt (levels b' side) x =
            if x = level.price.val then level.quantity.val else quantityAt (levels b side) x) ∧
          (∀ s, s ≠ side → levels b' s = levels b s) ∧
          r = .Ok (if quantityAt (levels b side) level.price.val = level.quantity.val then none
            else some { side, level })
      else r = .Err .PriceOutOfRange ∧ b' = b ⦄ := by
  unfold Book.set
  step with valid_price_spec as ⟨ ok, hok ⟩
  split
  · have hvp : ValidPrice level.price.val := by simp_all
    split
    · simp_all
    · have hq : ¬ level.quantity.val < 0 := by scalar_tac
      simp only [hq, ite_false]
      cases side
      · obtain ⟨hv, hva⟩ := hb
        simp only [levels] at hv hva ⊢
        step with lookup_spec as ⟨ lk, hlk ⟩
        · simpa [alloc.vec.Vec.deref] using hv.1
        simp only [alloc.vec.Vec.deref, Slice.from_val] at hlk
        cases lk with
        | Found i =>
          obtain ⟨hi, hpi⟩ := hlk
          have hqi := hv.1.quantityAt_found hi
          rw [hpi] at hqi
          step as ⟨ l1, hl1 ⟩
          split
          · simp only [WP.spec_ok, Book.Valid, levels]
            refine ⟨⟨hv, hva⟩, ?_, ?_, ?_⟩
            · intro x; split <;> simp_all
            · intro s hs; cases s <;> simp_all
            · simp_all
          · split
            · step as ⟨ rm, v1, hrm, hv1 ⟩
              obtain ⟨hve, hqe⟩ := hv.erase hi
              simp only [Book.Valid, levels]
              refine ⟨⟨by rw [hv1]; exact hve, hva⟩, ?_, ?_, ?_⟩
              · intro x; rw [hv1, hqe, hpi]; split <;> simp_all
              · intro s hs; cases s <;> simp_all
              · simp_all
            · step as ⟨ l2, back, hl2, hback ⟩
              have hq0 : 0 < level.quantity.val := by scalar_tac
              obtain ⟨hvu, hqu⟩ := hv.update hi (lv := { price := l2.price, quantity := level.quantity })
                (by simp_all) hq0
              simp only [Book.Valid, levels]
              refine ⟨⟨by simpa [hback] using hvu, hva⟩, ?_, ?_, ?_⟩
              · intro x; have := hqu x; simp_all
              · intro s hs; cases s <;> simp_all
              · simp_all
        | InsertAt i =>
          obtain ⟨hi, hbef, haft⟩ := hlk
          have hq0 := quantityAt_insert_pos hbef haft
          dsimp only
          split
          · simp only [WP.spec_ok, Book.Valid, levels]
            refine ⟨⟨hv, hva⟩, ?_, ?_, ?_⟩
            · intro x; split <;> simp_all
            · intro s hs; cases s <;> simp_all
            · simp_all
          · have hlen := hv.length_lt
            step as ⟨ ins, hins ⟩
            · simp [SCALE_val] at hlen; scalar_tac
            have hqpos : 0 < level.quantity.val := by scalar_tac
            obtain ⟨hvi, hqi⟩ := hv.insert hi hbef haft ⟨hvp, hqpos⟩
            simp only [Book.Valid, levels]
            refine ⟨⟨by rw [hins]; exact hvi, hva⟩, ?_, ?_, ?_⟩
            · intro x; rw [hins, hqi]
            · intro s hs; cases s <;> simp_all
            · simp_all; omega
      · obtain ⟨hva, hv⟩ := hb
        simp only [levels] at hv hva ⊢
        step with lookup_spec as ⟨ lk, hlk ⟩
        · simpa [alloc.vec.Vec.deref] using hv.1
        simp only [alloc.vec.Vec.deref, Slice.from_val] at hlk
        cases lk with
        | Found i =>
          obtain ⟨hi, hpi⟩ := hlk
          have hqi := hv.1.quantityAt_found hi
          rw [hpi] at hqi
          step as ⟨ l1, hl1 ⟩
          split
          · simp only [WP.spec_ok, Book.Valid, levels]
            refine ⟨⟨hva, hv⟩, ?_, ?_, ?_⟩
            · intro x; split <;> simp_all
            · intro s hs; cases s <;> simp_all
            · simp_all
          · split
            · step as ⟨ rm, v1, hrm, hv1 ⟩
              obtain ⟨hve, hqe⟩ := hv.erase hi
              simp only [Book.Valid, levels]
              refine ⟨⟨hva, by rw [hv1]; exact hve⟩, ?_, ?_, ?_⟩
              · intro x; rw [hv1, hqe, hpi]; split <;> simp_all
              · intro s hs; cases s <;> simp_all
              · simp_all
            · step as ⟨ l2, back, hl2, hback ⟩
              have hq0 : 0 < level.quantity.val := by scalar_tac
              obtain ⟨hvu, hqu⟩ := hv.update hi (lv := { price := l2.price, quantity := level.quantity })
                (by simp_all) hq0
              simp only [Book.Valid, levels]
              refine ⟨⟨hva, by simpa [hback] using hvu⟩, ?_, ?_, ?_⟩
              · intro x; have := hqu x; simp_all
              · intro s hs; cases s <;> simp_all
              · simp_all
        | InsertAt i =>
          obtain ⟨hi, hbef, haft⟩ := hlk
          have hq0 := quantityAt_insert_pos hbef haft
          dsimp only
          split
          · simp only [WP.spec_ok, Book.Valid, levels]
            refine ⟨⟨hva, hv⟩, ?_, ?_, ?_⟩
            · intro x; split <;> simp_all
            · intro s hs; cases s <;> simp_all
            · simp_all
          · have hlen := hv.length_lt
            step as ⟨ ins, hins ⟩
            · simp [SCALE_val] at hlen; scalar_tac
            have hqpos : 0 < level.quantity.val := by scalar_tac
            obtain ⟨hvi, hqi⟩ := hv.insert hi hbef haft ⟨hvp, hqpos⟩
            simp only [Book.Valid, levels]
            refine ⟨⟨hva, by rw [hins]; exact hvi⟩, ?_, ?_, ?_⟩
            · intro x; rw [hins, hqi]
            · intro s hs; cases s <;> simp_all
            · simp_all; omega
  · simp_all

end book_core.Spec
