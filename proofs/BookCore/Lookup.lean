import BookCore.Spec

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- If `a` is worse than `b` and `b` is worse than `c`, then `a` is worse than `c`. -/
theorem worse_transitive {side : Side} {a b c : Int} (h1 : Worse side a b) (h2 : Worse side b c) :
    Worse side a c := by
  cases side <;> simp only [Worse] at * <;> omega

/-- For any two prices, `a` is worse than `b`, `a` is equal to `b`, or `b` is worse than `a`. -/
theorem worse_trichotomy (side : Side) (a b : Int) :
    Worse side a b ∨ a = b ∨ Worse side b a := by
  cases side <;> simp only [Worse] <;> omega

/-- Given a sorted side, a later level has a worse price than an earlier one. -/
theorem Sorted.later_is_worse {side : Side} {l : List Level} (h : Sorted side l)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    Worse side l[j].price.val (l[i]'(by omega)).price.val := by
  unfold Sorted at h
  rw [List.pairwise_iff_getElem] at h
  exact h i j (by omega) hj hij

/-- `r` is the position of `price` in `l`, or where it should be inserted. -/
def _root_.book_core.Lookup.Correct (r : Lookup) (side : Side) (l : List Level) (price : Int) :
    Prop :=
  match r with
  | .Found i => ∃ h : i.val < l.length, l[i.val].price.val = price
  | .InsertAt i =>
    i.val ≤ l.length ∧
    (∀ j (h : j < l.length), j < i.val → Worse side price l[j].price.val) ∧
    (∀ j (h : j < l.length), i.val ≤ j → Worse side l[j].price.val price)

/-- Starting at `i`, the loop finds the position of `price` in `levels`, or where it should
    be inserted. Requires every level before `i` to have a better price. -/
theorem lookup_loop_spec (levels : Slice Level) (side : Side) (price : Std.I64) (i : Std.Usize)
    (hs : Sorted side levels.val) (hi : i.val ≤ levels.length)
    (hb : ∀ j (h : j < levels.length), j < i.val → Worse side price.val levels.val[j].price.val) :
    lookup_loop levels side price i ⦃ r => r.Correct side levels.val price.val ⦄ := by
  unfold lookup_loop
  apply loop.spec_decr_nat (fun x : Std.I64 × Std.Usize => levels.length - x.2.val)
    (fun x : Std.I64 × Std.Usize => x.1 = price ∧ x.2.val ≤ levels.length ∧
      ∀ j (h : j < levels.length), j < x.2.val → Worse side price.val levels.val[j].price.val)
  · rintro ⟨p, i⟩ ⟨hp, hi, hb⟩
    simp only at hp hi hb ⊢
    subst p
    unfold lookup_loop.body
    simp only [Slice.len]
    split
    · step as ⟨ l, hl ⟩
      split
      · simp only [WP.spec_ok, Lookup.Correct]
        exact ⟨by scalar_tac, by simp_all⟩
      · step with is_worse_spec as ⟨ b, hb' ⟩
        split
        · simp only [WP.spec_ok, Lookup.Correct]
          refine ⟨by scalar_tac, hb, ?_⟩
          intro j hj hij
          have hw : Worse side l.price.val price.val := by simp_all
          rcases Nat.lt_or_eq_of_le hij with hlt | heq
          · have := hs.later_is_worse hlt hj
            simp only [← hl] at this
            exact worse_transitive this hw
          · subst heq; simp_all
        · step as ⟨ i2, hi2 ⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro j hj hji
          have hnw : ¬ Worse side l.price.val price.val := by simp_all
          have hne : l.price.val ≠ price.val := by
            intro h; apply ‹¬ l.price = price›; scalar_tac
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by scalar_tac : j < i.val + 1)) with hlt | heq
          · exact hb j hj hlt
          · subst heq; simp only [← hl]
            rcases worse_trichotomy side l.price.val price.val with h | h | h
            · exact absurd h hnw
            · exact absurd h hne
            · exact h
    · simp only [WP.spec_ok, Lookup.Correct]
      refine ⟨hi, hb, ?_⟩
      intro j hj hij
      scalar_tac
  · exact ⟨rfl, hi, hb⟩

/-- `lookup` finds the position of `price` in `levels`, or where it should be inserted. -/
theorem lookup_spec (levels : Slice Level) (side : Side) (price : Std.I64)
    (hs : Sorted side levels.val) :
    lookup levels side price ⦃ r => r.Correct side levels.val price.val ⦄ := by
  unfold lookup
  apply lookup_loop_spec levels side price 0#usize hs (by simp)
  intro j _ hj
  simp at hj

end book_core.Spec
