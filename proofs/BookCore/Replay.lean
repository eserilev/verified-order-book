import BookCore.Delta

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- Two levels with the same price and the same quantity are the same level. -/
theorem Level.ext' {a b : Level} (hp : a.price.val = b.price.val)
    (hq : a.quantity.val = b.quantity.val) : a = b := by
  cases a; cases b
  simp only [Level.mk.injEq]
  exact ⟨(IScalar.eq_equiv _ _).mpr hp, (IScalar.eq_equiv _ _).mpr hq⟩

/-- Removing the best level from a valid side leaves a valid side. -/
theorem ValidSide.tail {side : Side} {a : Level} {l : List Level} (hv : ValidSide side (a :: l)) :
    ValidSide side l :=
  ⟨(List.pairwise_cons.mp hv.1).2, fun x hx => hv.2 x (List.mem_cons_of_mem a hx)⟩

/-- In a valid side, every level after the first has a worse price than the first. -/
theorem ValidSide.head_best {side : Side} {a : Level} {l : List Level}
    (hv : ValidSide side (a :: l)) : ∀ y ∈ l, Worse side y.price.val a.price.val :=
  (List.pairwise_cons.mp hv.1).1

/-- The quantity at the first level's price is the first level's quantity. -/
theorem quantityAt_cons_self (a : Level) (l : List Level) :
    quantityAt (a :: l) a.price.val = a.quantity.val := by
  rw [quantityAt_cons, ite_eq_left rfl]

/-- In a valid side, the quantity at any price better than the best level's price is 0. -/
theorem ValidSide.quantityAt_of_better {side : Side} {a : Level} {l : List Level}
    (hv : ValidSide side (a :: l)) {x : Int} (hx : Worse side a.price.val x) :
    quantityAt (a :: l) x = 0 := by
  apply quantityAt_eq_zero
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx.ne
  · exact (worse_transitive (hv.head_best y hy) hx).ne

/-- Given two valid sides, if `quantityAt` agrees at every price, the sides are equal. -/
theorem ValidSide.eq_of_quantityAt {side : Side} :
    ∀ {l₁ l₂ : List Level}, ValidSide side l₁ → ValidSide side l₂ →
      (∀ x, quantityAt l₁ x = quantityAt l₂ x) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: l₂, _, h₂, hq => by
    have := hq b.price.val
    rw [quantityAt_cons_self] at this
    have := (h₂.2 b (List.mem_cons_self)).2
    simp [quantityAt] at *; omega
  | a :: l₁, [], h₁, _, hq => by
    have := hq a.price.val
    rw [quantityAt_cons_self] at this
    have := (h₁.2 a (List.mem_cons_self)).2
    simp [quantityAt] at *; omega
  | a :: l₁, b :: l₂, h₁, h₂, hq => by
    have hpa := (h₁.2 a (List.mem_cons_self)).2
    have hpb := (h₂.2 b (List.mem_cons_self)).2
    have hp : a.price.val = b.price.val := by
      rcases worse_trichotomy side a.price.val b.price.val with h | h | h
      · have := hq b.price.val
        rw [quantityAt_cons_self, h₁.quantityAt_of_better h] at this
        omega
      · exact h
      · have := hq a.price.val
        rw [quantityAt_cons_self, h₂.quantityAt_of_better h] at this
        omega
    have hab : a = b := by
      apply Level.ext' hp
      have := hq a.price.val
      rwa [quantityAt_cons_self, hp, quantityAt_cons_self] at this
    subst hab
    congr 1
    apply ValidSide.eq_of_quantityAt h₁.tail h₂.tail
    intro x
    by_cases hx : a.price.val = x
    · subst hx
      rw [quantityAt_eq_zero (fun y hy => (h₁.head_best y hy).ne),
        quantityAt_eq_zero (fun y hy => (h₂.head_best y hy).ne)]
    · have := hq x
      rwa [quantityAt_cons, quantityAt_cons, ite_eq_right hx, ite_eq_right hx] at this

/-! ### Books -/

/-- Two books with the same bids and the same asks are the same book. -/
theorem Book.ext_levels {b₁ b₂ : Book} (hb : levels b₁ .Buy = levels b₂ .Buy)
    (ha : levels b₁ .Sell = levels b₂ .Sell) : b₁ = b₂ := by
  cases b₁; cases b₂
  simp only [levels] at hb ha
  simp only [Book.mk.injEq]
  exact ⟨alloc.vec.Vec.ext _ _ hb, alloc.vec.Vec.ext _ _ ha⟩

/-- `b'` is `b` with the quantity at `price` on `side` set to `q`. -/
def Changes (b : Book) (side : Side) (price q : Int) (b' : Book) : Prop :=
  b'.Valid ∧
  (∀ x, quantityAt (levels b' side) x =
    if x = price then q else quantityAt (levels b side) x) ∧
  (∀ s, s ≠ side → levels b' s = levels b s)

/-- Given a valid book, each of its sides is valid. -/
theorem _root_.book_core.Book.Valid.side {b : Book} (hb : b.Valid) : ∀ s, ValidSide s (levels b s)
  | .Buy => hb.1
  | .Sell => hb.2

/-- Only one book is `b` with the quantity at `price` set to `q`. -/
theorem Changes.unique {b b₁ b₂ : Book} {side : Side} {price q : Int}
    (h₁ : Changes b side price q b₁) (h₂ : Changes b side price q b₂) : b₁ = b₂ := by
  have hside : ∀ s, levels b₁ s = levels b₂ s := by
    intro s
    by_cases hs : s = side
    · subst hs
      apply ValidSide.eq_of_quantityAt (Book.Valid.side h₁.1 s) (Book.Valid.side h₂.1 s)
      intro x; rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2 s hs, h₂.2.2 s hs]
  exact Book.ext_levels (hside .Buy) (hside .Sell)

/-- Setting the quantity at `price` to the quantity already there gives back `b`. -/
theorem Changes.eq_self {b b' : Book} {side : Side} {price : Int} (hb : b.Valid)
    (h : Changes b side price (quantityAt (levels b side) price) b') : b' = b := by
  apply Changes.unique h
  refine ⟨hb, ?_, fun _ _ => rfl⟩
  intro x; split <;> simp_all

/-- Given a valid price and a quantity of 0 or more, `set` sets the quantity at
    `level.price` to `level.quantity`, and returns `None` when the book did not change. -/
theorem Book.set_changes (b : Book) (side : Side) (level : Level) (hb : b.Valid)
    (hp : ValidPrice level.price.val) (hq : 0 ≤ level.quantity.val) :
    b.set side level ⦃ r b' =>
      Changes b side level.price.val level.quantity.val b' ∧
      r = .Ok (if quantityAt (levels b side) level.price.val = level.quantity.val then none
        else some { side, level }) ⦄ := by
  apply WP.spec_mono (Book.set_spec b side level hb)
  rintro ⟨r, b'⟩ h
  have hq' : ¬ level.quantity.val < 0 := by omega
  simp only [hp, hq', ite_true, ite_false] at h
  exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

/-! ### Replay -/

/-- One call to `set` or `apply_delta`. -/
inductive Op where
  | set (side : Side) (level : Level)
  | delta (side : Side) (price delta : Std.I64)

/-- Runs one call on `b`. -/
def Op.run (b : Book) : Op → Result (core.result.Result (Option Update) Error × Book)
  | .set side level => b.set side level
  | .delta side price d => b.apply_delta side price d

/-- The updates a call emits. -/
def emitted : core.result.Result (Option Update) Error → List Update
  | .Ok (some u) => [u]
  | _ => []

/-- Runs `ops` on `b`, collecting the emitted updates. -/
def runOps (b : Book) : List Op → Result (Book × List Update)
  | [] => ok (b, [])
  | op :: ops => do
    let (r, b₁) ← op.run b
    let (b₂, us) ← runOps b₁ ops
    ok (b₂, emitted r ++ us)

/-- Applies each update to `b` with `set`. -/
def replay (b : Book) : List Update → Result Book
  | [] => ok b
  | u :: us => do
    let (_, b₁) ← b.set u.side u.level
    replay b₁ us

/-- Given a valid book, a call keeps it valid. If it emits nothing, the book did not
    change. If it emits an update, applying that update with `set` gives the same book. -/
theorem Op.run_spec (op : Op) (b : Book) (hb : b.Valid) :
    op.run b ⦃ r b₁ =>
      b₁.Valid ∧ (emitted r = [] → b₁ = b) ∧
      (∀ u, emitted r = [u] → b.set u.side u.level ⦃ _ b₁' => b₁' = b₁ ⦄) ⦄ := by
  cases op with
  | set side level =>
    apply WP.spec_mono (Book.set_spec b side level hb)
    rintro ⟨r, b₁⟩ h
    by_cases hp : ValidPrice level.price.val
    · by_cases hq : level.quantity.val < 0
      · simp only [hp, hq, ite_true] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [emitted, hb]
      · simp only [hp, hq, ite_true, ite_false] at h
        obtain ⟨hv, hqa, hs, hr⟩ := h
        have hc : Changes b side level.price.val level.quantity.val b₁ := ⟨hv, hqa, hs⟩
        refine ⟨hv, ?_, ?_⟩
        · intro he
          by_cases hsame : quantityAt (levels b side) level.price.val = level.quantity.val
          · rw [← hsame] at hc; exact hc.eq_self hb
          · simp [hr, hsame, emitted] at he
        · intro u hu
          by_cases hsame : quantityAt (levels b side) level.price.val = level.quantity.val
          · simp [hr, hsame, emitted] at hu
          · simp only [hr, hsame, ite_false, emitted, List.cons.injEq] at hu
            obtain ⟨rfl, -⟩ := hu
            apply WP.spec_mono (Book.set_changes b side level hb hp (by omega))
            rintro ⟨_, b₁'⟩ ⟨hc', -⟩
            exact hc'.unique hc
    · simp only [hp, ite_false] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [emitted, hb]
  | delta side price d =>
    apply WP.spec_mono (Book.apply_delta_spec b side price d hb)
    rintro ⟨r, b₁⟩ h
    by_cases hp : ValidPrice price.val
    · simp only [hp, ite_true] at h
      by_cases ho : quantityAt (levels b side) price.val + d.val > I64.max
      · simp only [ho, ite_true] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [emitted, hb]
      · simp only [ho, ite_false] at h
        by_cases hn : quantityAt (levels b side) price.val + d.val < 0
        · simp only [hn, ite_true] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [emitted, hb]
        · simp only [hn, ite_false] at h
          obtain ⟨hv, hqa, hs, q, hqv, hr⟩ := h
          have hc : Changes b side price.val (quantityAt (levels b side) price.val + d.val) b₁ :=
            ⟨hv, hqa, hs⟩
          refine ⟨hv, ?_, ?_⟩
          · intro he
            by_cases hd : d.val = 0
            · rw [hd, Int.add_zero] at hc; exact hc.eq_self hb
            · simp [hr, hd, emitted] at he
          · intro u hu
            by_cases hd : d.val = 0
            · simp [hr, hd, emitted] at hu
            · simp only [hr, hd, ite_false, emitted, List.cons.injEq] at hu
              obtain ⟨rfl, -⟩ := hu
              apply WP.spec_mono (Book.set_changes b side { price, quantity := q } hb hp
                (by simp only; omega))
              rintro ⟨_, b₁'⟩ ⟨hc', -⟩
              rw [hqv] at hc'
              exact hc'.unique hc
    · simp only [hp, ite_false] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [emitted, hb]

/-- Replaying the updates that `run` emits on the starting book gives the book `run` ends
    with. -/
theorem run_replay (ops : List Op) :
    ∀ b : Book, b.Valid →
      runOps b ops ⦃ p => p.1.Valid ∧ replay b p.2 ⦃ b' => b' = p.1 ⦄ ⦄ := by
  induction ops with
  | nil => intro b hb; simp [runOps, replay, WP.spec_ok, hb]
  | cons op ops ih =>
    intro b hb
    unfold runOps
    step with Op.run_spec op b hb as ⟨ r, b₁, hv₁, hnone, hsome ⟩
    step with ih b₁ hv₁ as ⟨ b₂, us, hv₂, hrep ⟩
    refine ⟨hv₂, ?_⟩
    cases hr : emitted r with
    | nil =>
      rw [hnone hr] at hrep
      simpa using hrep
    | cons u rest =>
      have hrest : rest = [] := by
        unfold emitted at hr; split at hr <;> simp_all
      subst hrest
      simp only [List.singleton_append, replay]
      step with hsome u hr as ⟨ _, b₁', hb₁' ⟩
      rw [hb₁']
      exact hrep

end book_core.Spec
