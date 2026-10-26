import BookCore.Delta

open Aeneas Aeneas.Std Result

namespace book_core.Spec

/-- Whether byte `c` is one of `'0'` to `'9'`. -/
def IsDigit (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

/-- Lets `IsDigit` be checked with `decide`. -/
instance (c : Nat) : Decidable (IsDigit c) := by
  unfold IsDigit; infer_instance

/-- The digits in `l` read as one number. -/
def digitsVal (l : List Nat) : Nat := l.foldl (fun acc c => acc * 10 + (c - 48)) 0

/-- Appending digit `c` multiplies the number by 10 and adds `c`. -/
theorem digitsVal_concat (l : List Nat) (c : Nat) :
    digitsVal (l ++ [c]) = digitsVal l * 10 + (c - 48) := by
  simp [digitsVal, List.foldl_append]

/-- Appending `n` zeros multiplies the number by `10 ^ n`. -/
theorem digitsVal_zeros (l : List Nat) (n : Nat) :
    digitsVal (l ++ List.replicate n 48) = digitsVal l * 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, digitsVal_concat, ih]
    ring

/-- `s` is a decimal string `a` or `a.b`, where `a` and `b` are digits and not both empty,
    and its exact value is `v / SCALE`. -/
def DecimalValue (s : List Nat) (v : Int) : Prop :=
  ∃ a b, ((s = a ∧ b = []) ∨ s = a ++ 46 :: b) ∧ (∀ c ∈ a ++ b, IsDigit c) ∧
    (∃ c ∈ a ++ b, IsDigit c) ∧ v * 10 ^ b.length = digitsVal (a ++ b) * 10 ^ 6

/-- What `parse_digits` knows after reading the prefix `p`. -/
def DigitsInv (p : List Nat) (d : Digits) : Prop :=
  (d.any_digit = true ↔ ∃ c ∈ p, IsDigit c) ∧
  if d.seen_dot then
    ∃ a b z, p = a ++ 46 :: (b ++ List.replicate z 48) ∧ (∀ c ∈ a ++ b, IsDigit c) ∧
      b.length ≤ 6 ∧ (0 < z → b.length = 6) ∧
      d.value.val = digitsVal (a ++ b) ∧ d.decimals.val = b.length
  else
    (∀ c ∈ p, IsDigit c) ∧ d.value.val = digitsVal p ∧ d.decimals.val = 0

/-- The parser's starting state is correct for the empty string. -/
theorem DigitsInv.nil : DigitsInv [] ⟨0#i64, 0#u32, false, false⟩ := by
  simp [DigitsInv, digitsVal]

/-- `u8::is_ascii_digit` returns whether `c` is one of `'0'` to `'9'`. -/
theorem U8.is_ascii_digit_spec (c : Std.U8) :
    core.num.U8.is_ascii_digit c ⦃ b => b = decide (IsDigit c.val) ⦄ := by
  simp [core.num.U8.is_ascii_digit, IsDigit, WP.spec_ok]

/-- If `x` is at most `n / 10`, then `x * 10` is at most `n`. -/
theorem mul_ten_le_of_le_tdiv {x n : Int} (hn : 0 ≤ n) (h : x ≤ n.tdiv 10) : x * 10 ≤ n := by
  rw [Int.tdiv_eq_ediv_of_nonneg hn] at h
  have := Int.mul_le_of_le_ediv (by norm_num) h
  omega

set_option maxRecDepth 100000 in
/-- Given that `read_char` returns `Ok d'`, reading `c` after `p` gives state `d'`. -/
theorem read_char_spec (p : List Nat) (d : Digits) (c : Std.U8) (h : DigitsInv p d) :
    read_char d c ⦃ r => ∀ d', r = .Ok d' → DigitsInv (p ++ [c.val]) d' ⦄ := by
  obtain ⟨hany, hrest⟩ := h
  unfold read_char
  split
  · rename_i hc
    have hc' : c.val = 46 := by scalar_tac
    split
    · simp [WP.spec_ok]
    · rename_i hs
      simp only [WP.spec_ok, core.result.Result.Ok.injEq, forall_eq']
      simp only [hs, Bool.false_eq_true, ite_false] at hrest
      obtain ⟨hdig, hval, hdec⟩ := hrest
      refine ⟨?_, ?_⟩
      · rw [hany]; simp [hc', IsDigit]
      · simp only [ite_true]
        exact ⟨p, [], 0, by simp [hc'], by simpa using hdig, by simp, by simp,
          by simpa using hval, by simpa using hdec⟩
  · rename_i hc
    step with U8.is_ascii_digit_spec as ⟨ b, hb ⟩
    split
    · rename_i hbt
      have hd : IsDigit c.val := by simp_all
      step as ⟨ i, hi ⟩
      step with UScalar.hcast_inBounds_spec as ⟨ digit, hdigit ⟩
      have hcd : c.val - 48 = digit.val := by scalar_tac
      have hany' : ∃ x ∈ p ++ [c.val], IsDigit x := ⟨c.val, by simp, hd⟩
      have hmax := I64_MAX_val
      split
      · rename_i hs
        simp only [hs, ite_true] at hrest
        obtain ⟨a, bs, z, hp, hab, hb6, hz, hv, hdec⟩ := hrest
        split
        · rename_i h6
          split
          · simp [WP.spec_ok]
          · rename_i h0
            have hc48 : c.val = 48 := by simp at h0; scalar_tac
            simp only [WP.spec_ok, core.result.Result.Ok.injEq, forall_eq']
            refine ⟨by simpa using hany', ?_⟩
            simp only [hs, ite_true]
            refine ⟨a, bs, z + 1, ?_, hab, hb6, fun _ => by scalar_tac, hv, hdec⟩
            rw [hp, hc48, List.replicate_succ']
            simp
        · rename_i h6
          step as ⟨ i1, hi1 ⟩
          step as ⟨ i2, hi2 ⟩
          split
          · simp [WP.spec_ok]
          · rename_i hov
            have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
            have hbound : d.value.val * 10 + digit.val ≤ I64.max := by
              have hle : d.value.val ≤ i2.val := by scalar_tac
              rw [hi2] at hle
              have h9 : (9 : Int) ≤ I64.rMax := by simp [I64.rMax]
              have hd9 : digit.val ≤ 9 := by simp only [IsDigit] at hd; omega
              have := mul_ten_le_of_le_tdiv (n := i1.val) (by omega) hle
              omega
            simp only [hs]
            step as ⟨ dec', hdec' ⟩
            step as ⟨ i3, hi3 ⟩
            step as ⟨ i4, hi4 ⟩
            simp only [core.result.Result.Ok.injEq, forall_eq']
            have hz0 : z = 0 := by
              rcases Nat.eq_zero_or_pos z with h | h
              · exact h
              · have := hz h; scalar_tac
            subst hz0
            refine ⟨by simpa using hany', ?_⟩
            simp only [ite_true]
            refine ⟨a, bs ++ [c.val], 0, by simp [hp], ?_, by simp; scalar_tac,
              by simp, ?_, by simp; scalar_tac⟩
            · intro x hx
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx | rfl
              · exact hab x (List.mem_append_left _ hx)
              · exact hab x (List.mem_append_right _ hx)
              · exact hd
            · rw [← List.append_assoc, digitsVal_concat]
              push_cast
              scalar_tac
      · rename_i hs
        simp only [hs, Bool.false_eq_true, ite_false] at hrest
        obtain ⟨hdig, hv, hdec⟩ := hrest
        step as ⟨ i1, hi1 ⟩
        step as ⟨ i2, hi2 ⟩
        split
        · simp [WP.spec_ok]
        · rename_i hov
          have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
          have hbound : d.value.val * 10 + digit.val ≤ I64.max := by
            have hle : d.value.val ≤ i2.val := by scalar_tac
            rw [hi2] at hle
            have h9 : (9 : Int) ≤ I64.rMax := by simp [I64.rMax]
            have hd9 : digit.val ≤ 9 := by simp only [IsDigit] at hd; omega
            have := mul_ten_le_of_le_tdiv (n := i1.val) (by omega) hle
            omega
          simp only [hs]
          step as ⟨ i3, hi3 ⟩
          step as ⟨ i4, hi4 ⟩
          simp only [core.result.Result.Ok.injEq, forall_eq']
          refine ⟨by simpa using hany', ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          refine ⟨?_, ?_, hdec⟩
          · intro x hx
            simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hdig x hx
            · exact hd
          · rw [digitsVal_concat]
            push_cast
            scalar_tac
    · simp [WP.spec_ok]

/-- The number for `l₁ ++ l₂` is the number for `l₁` shifted left by the length of `l₂`,
    plus the number for `l₂`. -/
theorem digitsVal_append (l₁ l₂ : List Nat) :
    digitsVal (l₁ ++ l₂) = digitsVal l₁ * 10 ^ l₂.length + digitsVal l₂ := by
  induction l₂ using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton l c ih =>
    rw [← List.append_assoc, digitsVal_concat, ih, digitsVal_concat, List.length_append,
      List.length_singleton, pow_succ]
    ring

/-- Appending digits never makes the number smaller. -/
theorem digitsVal_le_append (l₁ l₂ : List Nat) : digitsVal l₁ ≤ digitsVal (l₁ ++ l₂) := by
  rw [digitsVal_append]
  have : 1 ≤ 10 ^ l₂.length := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

/-- `n` digits make a number below `10 ^ n`. -/
theorem digitsVal_lt {l : List Nat} (h : ∀ c ∈ l, IsDigit c) : digitsVal l < 10 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton l c ih =>
    have hc := h c (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    rw [digitsVal_concat, List.length_append, List.length_singleton, pow_succ]
    simp only [IsDigit] at hc
    omega

/-- If digits make the number 0, every digit is `'0'`. -/
theorem eq_zero_of_digitsVal_eq_zero {l : List Nat} (h : ∀ c ∈ l, IsDigit c)
    (h0 : digitsVal l = 0) : ∀ c ∈ l, c = 48 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l c ih =>
    rw [digitsVal_concat] at h0
    have hc := h c (by simp)
    simp only [IsDigit] at hc
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (fun y hy => h y (by simp [hy])) (by omega) x hx
    · omega

/-- `s` is `a` or `a.b` with digits `a` and `b`, not both empty, no non-zero digit past the
    6th decimal place, and its value fits in an `I64`. -/
def WellFormed (s : List Nat) : Prop :=
  ∃ a b, ((s = a ∧ b = []) ∨ s = a ++ 46 :: b) ∧ (∀ c ∈ a ++ b, IsDigit c) ∧
    (∃ c ∈ a ++ b, IsDigit c) ∧ (∀ c ∈ b.drop 6, c = 48) ∧
    (digitsVal (a ++ b.take 6) : Int) ≤ I64.max

/-- A decimal string with an exact value that fits in an `I64` is well formed. -/
theorem DecimalValue.wellFormed {s : List Nat} {v : Int} (h : DecimalValue s v)
    (hv : v ≤ I64.max) : WellFormed s := by
  obtain ⟨a, b, hs, hdig, hex, heq⟩ := h
  have htd : b = b.take 6 ++ b.drop 6 := (List.take_append_drop 6 b).symm
  have hdig6 : ∀ c ∈ a ++ b.take 6, IsDigit c := fun c hc => by
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hdig c (List.mem_append_left _ hc)
    · exact hdig c (List.mem_append_right _ (List.mem_of_mem_take hc))
  have hdigd : ∀ c ∈ b.drop 6, IsDigit c := fun c hc =>
    hdig c (List.mem_append_right _ (List.mem_of_mem_drop hc))
  have hsplit : digitsVal (a ++ b) =
      digitsVal (a ++ b.take 6) * 10 ^ (b.drop 6).length + digitsVal (b.drop 6) := by
    conv => lhs; rw [htd, ← List.append_assoc]
    exact digitsVal_append _ _
  have hlen : b.length = (b.take 6).length + (b.drop 6).length := by
    rw [List.length_take, List.length_drop]; omega
  -- The digits past the 6th decimal place are all 0.
  have hzero : digitsVal (b.drop 6) = 0 := by
    by_cases hk : (b.drop 6).length = 0
    · rw [List.length_eq_zero_iff] at hk; rw [hk]; simp [digitsVal]
    · have ht6 : (b.take 6).length = 6 := by
        rw [List.length_take]; simp [List.length_drop] at hk; omega
      rw [hlen, ht6, pow_add, hsplit] at heq
      have hlt := digitsVal_lt hdigd
      set k := (b.drop 6).length
      set X := digitsVal (a ++ b.take 6)
      set Y := digitsVal (b.drop 6)
      have hpos : (0 : Int) < 10 ^ k := by positivity
      have h1 : v * 10 ^ k = X * 10 ^ k + Y := by
        have : (10 : Int) ^ 6 ≠ 0 := by norm_num
        apply mul_right_cancel₀ this
        push_cast at heq ⊢
        linarith [heq]
      have h2 : (Y : Int) = (v - X) * 10 ^ k := by linarith
      have hY0 : (0 : Int) ≤ Y := by positivity
      have hYlt : (Y : Int) < 10 ^ k := by exact_mod_cast hlt
      have hvX : v - X = 0 := by
        rcases lt_trichotomy (v - X) 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      have : (Y : Int) = 0 := by rw [h2, hvX]; ring
      exact_mod_cast this
  have hzeros := eq_zero_of_digitsVal_eq_zero hdigd hzero
  refine ⟨a, b, hs, hdig, hex, hzeros, ?_⟩
  -- The digits up to the 6th decimal place are at most `v`.
  rw [hsplit, hzero, hlen] at heq
  have ht6 : (b.take 6).length ≤ 6 := by rw [List.length_take]; omega
  set X := digitsVal (a ++ b.take 6)
  set t := (b.take 6).length
  set k := (b.drop 6).length
  have heq' : v * 10 ^ t = X * 10 ^ 6 := by
    have : (10 : Int) ^ k ≠ 0 := by positivity
    apply mul_right_cancel₀ this
    push_cast at heq ⊢
    rw [pow_add] at heq
    linarith [heq]
  have h6 : (10 : Int) ^ 6 = 10 ^ t * 10 ^ (6 - t) := by rw [← pow_add]; congr 1; omega
  have hv' : v = X * 10 ^ (6 - t) := by
    have : (10 : Int) ^ t ≠ 0 := by positivity
    apply mul_right_cancel₀ this
    rw [heq', h6]; ring
  have : (1 : Int) ≤ 10 ^ (6 - t) := one_le_pow₀ (by norm_num)
  have hX : (0 : Int) ≤ X := by positivity
  nlinarith

/-- Reading `c` after `d` succeeds. `c` is the first dot, or a digit that does not overflow
    and is 0 if past the 6th decimal place. -/
def CharOk (d : Digits) (c : Nat) : Prop :=
  (c = 46 ∧ d.seen_dot = false) ∨
  (IsDigit c ∧ (d.seen_dot = true ∧ d.decimals.val = 6 → c = 48) ∧
    (¬(d.seen_dot = true ∧ d.decimals.val = 6) → d.value.val * 10 + ((c : Int) - 48) ≤ I64.max))

/-- If `x` is more than `n / 10`, then `x * 10` is more than `n`. -/
theorem lt_mul_ten_of_tdiv_lt {x n : Int} (hn : 0 ≤ n) (h : n.tdiv 10 < x) : n < x * 10 := by
  rw [Int.tdiv_eq_ediv_of_nonneg hn] at h
  omega

/-- The value read so far is 0 or more. -/
theorem DigitsInv.value_nonneg {p : List Nat} {d : Digits} (h : DigitsInv p d) :
    0 ≤ d.value.val := by
  obtain ⟨-, hrest⟩ := h
  split at hrest
  · obtain ⟨_, _, _, _, _, _, _, hval, _⟩ := hrest; rw [hval]; positivity
  · rw [hrest.2.1]; positivity

set_option maxRecDepth 100000 in
/-- Given that `read_char` fails, `c` was not `CharOk`. -/
theorem read_char_err_spec (p : List Nat) (d : Digits) (c : Std.U8) (h : DigitsInv p d) :
    read_char d c ⦃ r => ∀ e, r = .Err e → ¬ CharOk d c.val ⦄ := by
  have hv0 := h.value_nonneg
  unfold read_char
  split
  · have hc' : c.val = 46 := by scalar_tac
    split
    · simp_all [WP.spec_ok, CharOk, IsDigit]
    · simp [WP.spec_ok]
  · rename_i hc
    have hc' : c.val ≠ 46 := by intro h; apply hc; scalar_tac
    step with U8.is_ascii_digit_spec as ⟨ b, hb ⟩
    split
    · have hd : IsDigit c.val := by simp_all
      step as ⟨ i, hi ⟩
      step with UScalar.hcast_inBounds_spec as ⟨ digit, hdigit ⟩
      have hcd : (c.val : Int) - 48 = digit.val := by scalar_tac
      have hmax := I64_MAX_val
      have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
      have h9 : (9 : Int) ≤ I64.rMax := by simp [I64.rMax]
      have hd9 : digit.val ≤ 9 := by simp only [IsDigit] at hd; omega
      have hd0 : 0 ≤ digit.val := by scalar_tac
      split
      · rename_i hs
        split
        · rename_i h6
          split
          · rename_i h0
            simp only [WP.spec_ok, core.result.Result.Err.injEq, forall_eq']
            simp only [CharOk, hc', false_and, false_or, not_and]
            intro _ h48
            have : d.decimals.val = 6 := by scalar_tac
            have := h48 ⟨hs, this⟩
            simp at h0; scalar_tac
          · simp [WP.spec_ok]
        · rename_i h6
          step as ⟨ i1, hi1 ⟩
          step as ⟨ i2, hi2 ⟩
          split
          · rename_i hov
            simp only [WP.spec_ok, core.result.Result.Err.injEq, forall_eq']
            simp only [CharOk, hc', false_and, false_or, not_and]
            intro _ _ hb'
            have hlt : i2.val < d.value.val := by scalar_tac
            rw [hi2] at hlt
            have := lt_mul_ten_of_tdiv_lt (n := i1.val) (by omega) hlt
            have h6' : ¬ (d.decimals.val = 6) := fun h => h6 ((UScalar.eq_equiv _ _).mpr (by simpa using h))
            have := hb' (fun _ => h6')
            omega
          · rename_i hov
            have hle : d.value.val ≤ i2.val := by scalar_tac
            rw [hi2] at hle
            have := mul_ten_le_of_le_tdiv (n := i1.val) (by omega) hle
            simp only [hs]
            step as ⟨ dec', hdec' ⟩
            step as ⟨ i3, hi3 ⟩
            step as ⟨ i4, hi4 ⟩
            simp
      · rename_i hs
        step as ⟨ i1, hi1 ⟩
        step as ⟨ i2, hi2 ⟩
        split
        · rename_i hov
          simp only [WP.spec_ok, core.result.Result.Err.injEq, forall_eq']
          simp only [CharOk, hc', false_and, false_or, not_and]
          intro _ _ hb'
          have hlt : i2.val < d.value.val := by scalar_tac
          rw [hi2] at hlt
          have := lt_mul_ten_of_tdiv_lt (n := i1.val) (by omega) hlt
          have := hb' (by simp [hs])
          omega
        · rename_i hov
          have hle : d.value.val ≤ i2.val := by scalar_tac
          rw [hi2] at hle
          have := mul_ten_le_of_le_tdiv (n := i1.val) (by omega) hle
          simp only [hs]
          step as ⟨ i3, hi3 ⟩
          step as ⟨ i4, hi4 ⟩
          simp
    · rename_i hbf
      have hnd : ¬ IsDigit c.val := by simp_all
      simp [WP.spec_ok, CharOk, hc', hnd]

/-- A digit is not a dot. -/
theorem IsDigit.ne_dot {c : Nat} (h : IsDigit c) : c ≠ 46 := by
  simp only [IsDigit] at h; omega

/-- If `a` and `a'` have no dot and `a ++ '.' :: x = a' ++ '.' :: y`, then `a = a'` and
    `x = y`. -/
theorem split_at_dot {a a' x y : List Nat} (ha : ∀ c ∈ a, c ≠ 46) (ha' : ∀ c ∈ a', c ≠ 46)
    (h : a ++ 46 :: x = a' ++ 46 :: y) : a = a' ∧ x = y := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons c a' => simp at h; exact absurd h.1 (ha' c (by simp))
  | cons c a ih =>
    cases a' with
    | nil => simp at h; exact absurd h.1 (ha c (by simp))
    | cons c' a' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun x hx => ha x (by simp [hx])) (fun x hx => ha' x (by simp [hx])) h
      exact ⟨by rw [this.1], this.2⟩

/-- Given a prefix with only digits, the parser has not seen a dot, and its value is those
    digits. -/
theorem DigitsInv.of_digits {p : List Nat} {d : Digits} (hd : DigitsInv p d)
    (h : ∀ c ∈ p, IsDigit c) :
    d.seen_dot = false ∧ d.value.val = digitsVal p ∧ d.decimals.val = 0 := by
  obtain ⟨-, hrest⟩ := hd
  by_cases hs : d.seen_dot
  · simp only [hs, ite_true] at hrest
    obtain ⟨a, _, _, hp, _⟩ := hrest
    exact absurd (h 46 (by simp [hp])) (by simp [IsDigit])
  · simp only [hs, Bool.false_eq_true, ite_false] at hrest
    simp only [Bool.not_eq_true] at hs
    exact ⟨hs, hrest.2.1, hrest.2.2⟩

/-- Reading one more character adds that digit to the number. -/
theorem digitsVal_take_succ {l : List Nat} {i : Nat} (hi : i < l.length) :
    digitsVal (l.take i) * 10 + (l[i] - 48) = digitsVal (l.take (i + 1)) := by
  rw [List.take_succ_eq_append_getElem hi, digitsVal_concat]

/-- In a well formed string, every character is `CharOk` for the state the parser is in. -/
theorem WellFormed.charOk {L : List Nat} (hwf : WellFormed L) {i : Nat} (hi : i < L.length)
    {d : Digits} (hd : DigitsInv (L.take i) d) : CharOk d L[i] := by
  obtain ⟨a, b, hs, hdig, -, hzeros, hmax⟩ := hwf
  have hda : ∀ c ∈ a, IsDigit c := fun c hc => hdig c (List.mem_append_left _ hc)
  have hdb : ∀ c ∈ b, IsDigit c := fun c hc => hdig c (List.mem_append_right _ hc)
  have hamax : (digitsVal a : Int) ≤ I64.max :=
    le_trans (by exact_mod_cast digitsVal_le_append a (b.take 6)) hmax
  -- Before the dot, `c` is a digit of `a` and the value so far is a prefix of `a`.
  have before : ∀ (hj : i < a.length), L.take i = a.take i → L[i] = a[i] → CharOk d L[i] := by
    intro hj htk hc
    have hdt : ∀ c ∈ a.take i, IsDigit c := fun c hc => hda c (List.mem_of_mem_take hc)
    rw [htk] at hd
    obtain ⟨hns, hval, hdec⟩ := hd.of_digits hdt
    have hcd : IsDigit a[i] := hda _ (List.getElem_mem hj)
    rw [hc]
    refine Or.inr ⟨hcd, by simp [hns], fun _ => ?_⟩
    rw [hval]
    have h48 : 48 ≤ a[i] := hcd.1
    have hsum := digitsVal_take_succ hj
    have hle := digitsVal_le_append (a.take (i + 1)) (a.drop (i + 1))
    rw [List.take_append_drop] at hle
    have : ((digitsVal (a.take i) : Int) * 10 + ((a[i] : Int) - 48)) =
        (digitsVal (a.take (i + 1)) : Int) := by
      rw [← hsum]; push_cast; omega
    rw [this]
    exact le_trans (by exact_mod_cast hle) hamax
  rcases hs with ⟨rfl, rfl⟩ | rfl
  · exact before hi rfl rfl
  · rcases lt_trichotomy i a.length with h | rfl | h
    · exact before h (by rw [List.take_append_of_le_length (by omega)])
        (by rw [List.getElem_append_left h])
    · rw [List.take_left] at hd
      obtain ⟨hns, -, -⟩ := hd.of_digits hda
      left
      exact ⟨by simp, hns⟩
    · -- After the dot, `c` is a digit of `b`.
      set k := i - a.length - 1 with hk
      have hkb : k < b.length := by simp at hi; omega
      have htk : (a ++ 46 :: b).take i = a ++ 46 :: b.take k := by
        rw [List.take_append, List.take_of_length_le (by omega)]
        have : i - a.length = k + 1 := by omega
        rw [this, List.take_succ_cons]
      have hc : (a ++ 46 :: b)[i] = b[k] := by
        rw [List.getElem_append_right (by omega)]
        have : i - a.length = k + 1 := by omega
        simp only [this, List.getElem_cons_succ]
      rw [hc]
      have hcd : IsDigit b[k] := hdb _ (List.getElem_mem hkb)
      rw [htk] at hd
      obtain ⟨hiff, hrest⟩ := hd
      by_cases hsd : d.seen_dot
      · simp only [hsd, ite_true] at hrest
        obtain ⟨a', bs, z, hp, hab', hb6, hz, hval, hdec⟩ := hrest
        have hna' : ∀ c ∈ a', c ≠ 46 := fun c hc => (hab' c (List.mem_append_left _ hc)).ne_dot
        have hna : ∀ c ∈ a, c ≠ 46 := fun c hc => (hda c hc).ne_dot
        obtain ⟨rfl, hbz⟩ := split_at_dot hna hna' hp
        have hlenk : k = bs.length + z := by
          have := congrArg List.length hbz
          simp [List.length_take] at this; omega
        refine Or.inr ⟨hcd, fun ⟨_, h6⟩ => ?_, fun hn => ?_⟩
        · apply hzeros
          have : 6 ≤ k := by omega
          rw [List.mem_drop_iff_getElem]
          exact ⟨k - 6, by omega, by congr 1; omega⟩
        · have h6 : bs.length ≠ 6 := fun h => hn ⟨hsd, by omega⟩
          have hz0 : z = 0 := by
            rcases Nat.eq_zero_or_pos z with h | h
            · exact h
            · exact absurd (hz h) h6
          subst hz0
          simp only [List.replicate_zero, List.append_nil] at hbz
          have hk6 : k < 6 := by omega
          rw [hval, ← hbz]
          have h48 : 48 ≤ b[k] := hcd.1
          have hstep : (digitsVal (a ++ b.take k) : Int) * 10 + ((b[k] : Int) - 48) =
              digitsVal (a ++ b.take (k + 1)) := by
            rw [List.take_succ_eq_append_getElem hkb, ← List.append_assoc, digitsVal_concat]
            push_cast; omega
          have htt : (b.take 6).take (k + 1) = b.take (k + 1) := by
            rw [List.take_take]; congr 1; omega
          have hle := digitsVal_le_append (a ++ b.take (k + 1)) ((b.take 6).drop (k + 1))
          have hrhs : b.take (k + 1) ++ (b.take 6).drop (k + 1) = b.take 6 := by
            rw [← htt, List.take_append_drop]
          rw [List.append_assoc, hrhs] at hle
          rw [hstep]
          exact le_trans (by exact_mod_cast hle) hmax
      · have hnd : ¬ ∀ c ∈ a ++ 46 :: b.take k, IsDigit c := fun h =>
          absurd (h 46 (by simp)) (by simp [IsDigit])
        simp only [hsd, Bool.false_eq_true, ite_false] at hrest
        exact absurd hrest.1 hnd

/-- Given a `CharOk` character, `read_char` succeeds. -/
theorem read_char_ok_spec (p : List Nat) (d : Digits) (c : Std.U8) (h : DigitsInv p d)
    (hc : CharOk d c.val) :
    read_char d c ⦃ r => ∃ d', r = .Ok d' ∧ DigitsInv (p ++ [c.val]) d' ⦄ := by
  apply WP.spec_mono (WP.spec_and (read_char_spec p d c h) (read_char_err_spec p d c h))
  rintro r ⟨h1, h2⟩
  cases r with
  | Ok d' => exact ⟨d', rfl, h1 d' rfl⟩
  | Err e => exact absurd hc (h2 e rfl)

/-- Starting at `i`, given that the loop returns `Ok`, the final state is correct for `s`. -/
theorem parse_digits_loop_spec (s : Slice Std.U8) (d : Digits) (i : Std.Usize)
    (hi : i.val ≤ s.length) (hd : DigitsInv ((s.val.take i.val).map (·.val)) d) :
    parse_digits_loop s d i ⦃ r => ∀ v dec, r = .Ok (v, dec) →
      ∃ d', DigitsInv (s.val.map (·.val)) d' ∧ d'.any_digit = true ∧ d'.value = v ∧
        d'.decimals = dec ⦄ := by
  unfold parse_digits_loop
  apply loop.spec_decr_nat (fun x : Digits × Std.Usize => s.length - x.2.val)
    (fun x : Digits × Std.Usize => x.2.val ≤ s.length ∧
      DigitsInv ((s.val.take x.2.val).map (·.val)) x.1)
  · rintro ⟨d, i⟩ ⟨hi, hd⟩
    simp only at hi hd ⊢
    unfold parse_digits_loop.body
    simp only [Slice.len]
    split
    · step as ⟨ x, hx ⟩
      step with read_char_spec _ d x hd as ⟨ r, hr ⟩
      step as ⟨ cf, hcf ⟩
      cases r with
      | Ok d' =>
        simp only at hcf
        subst hcf
        simp only
        step as ⟨ i3, hi3 ⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hnext := hr d' rfl
        have htake : s.val.take i3.val = s.val.take i.val ++ [x] := by
          rw [hi3, List.take_succ_eq_append_getElem (by scalar_tac), hx]
        rw [htake, List.map_append]
        simpa using hnext
      | Err e =>
        simp only at hcf
        subst hcf
        simp only
        step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
          _ (core.convert.FromSame Error) e e rfl as ⟨ out, hout ⟩
        simp [hout]
    · have hlen : i.val = s.length := by scalar_tac
      have hall : s.val.take i.val = s.val := by rw [hlen]; simp
      rw [hall] at hd
      split
      · simp only [WP.spec_ok, core.result.Result.Ok.injEq, Prod.mk.injEq]
        rintro v dec ⟨rfl, rfl⟩
        exact ⟨d, hd, by assumption, rfl, rfl⟩
      · simp [WP.spec_ok]
  · exact ⟨hi, hd⟩

/-- Given that `parse_digits` returns `Ok`, the final state is correct for `s`. -/
theorem parse_digits_spec (s : Slice Std.U8) :
    parse_digits s ⦃ r => ∀ v dec, r = .Ok (v, dec) →
      ∃ d', DigitsInv (s.val.map (·.val)) d' ∧ d'.any_digit = true ∧ d'.value = v ∧
        d'.decimals = dec ⦄ := by
  unfold parse_digits
  apply parse_digits_loop_spec s _ 0#usize (by simp)
  simpa using DigitsInv.nil

/-- Given that `scale_up` returns `Ok v`, `v` is `value` with `6 - decimals` zeros added. -/
theorem scale_up_spec (value : Std.I64) (decimals : Std.U32) (hdec : decimals.val ≤ 6)
    (hv : 0 ≤ value.val) :
    scale_up value decimals ⦃ r => ∀ v, r = .Ok v →
      v.val = value.val * 10 ^ (6 - decimals.val) ⦄ := by
  unfold scale_up scale_up_loop
  apply loop.spec_decr_nat (fun x : Std.I64 × Std.U32 => 6 - x.2.val)
    (fun x : Std.I64 × Std.U32 => x.2.val ≤ 6 ∧ 0 ≤ x.1.val ∧
      x.1.val * 10 ^ (6 - x.2.val) = value.val * 10 ^ (6 - decimals.val))
  · rintro ⟨w, k⟩ ⟨hk, hw, heq⟩
    simp only at hk hw heq ⊢
    unfold scale_up_loop.body
    split
    · have hmax := I64_MAX_val
      step as ⟨ m, hm ⟩
      split
      · simp [WP.spec_ok]
      · rename_i hov
        have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
        have hle : w.val ≤ m.val := by scalar_tac
        rw [hm] at hle
        have h9 : (0 : Int) ≤ I64.rMax := by simp [I64.rMax]
        have := mul_ten_le_of_le_tdiv (n := I64.rMax) h9 hle
        step as ⟨ w', hw' ⟩
        step as ⟨ k', hk' ⟩
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [hw', hk', ← heq]
        have h6 : 6 - k.val = (6 - (k.val + 1)) + 1 := by scalar_tac
        rw [h6, pow_succ]
        ring
    · have hk6 : k.val = 6 := by scalar_tac
      simp only [WP.spec_ok, core.result.Result.Ok.injEq]
      rintro v rfl
      rw [← heq, hk6]
      simp
  · exact ⟨hdec, hv, rfl⟩

/-- Given a final state with a digit, `value` with zeros added to 6 decimals is the exact
    value of `p`. -/
theorem DigitsInv.decimalValue {p : List Nat} {d : Digits} (h : DigitsInv p d)
    (hany : d.any_digit = true) {v : Int} (hv : v = d.value.val * 10 ^ (6 - d.decimals.val)) :
    DecimalValue p v := by
  obtain ⟨hiff, hrest⟩ := h
  have hex := hiff.mp hany
  by_cases hs : d.seen_dot
  · simp only [hs, ite_true] at hrest
    obtain ⟨a, bs, z, hp, hab, hb6, -, hval, hdec⟩ := hrest
    refine ⟨a, bs ++ List.replicate z 48, Or.inr hp, ?_, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_append, List.mem_replicate] at hc
      rcases hc with hc | hc | ⟨-, rfl⟩
      · exact hab c (List.mem_append_left _ hc)
      · exact hab c (List.mem_append_right _ hc)
      · simp [IsDigit]
    · obtain ⟨c, hc, hdc⟩ := hex
      refine ⟨c, ?_, hdc⟩
      rw [hp] at hc
      simp only [List.mem_append, List.mem_cons] at hc ⊢
      rcases hc with hc | rfl | hc
      · exact Or.inl hc
      · simp [IsDigit] at hdc
      · exact Or.inr hc
    · rw [hv, hval, hdec, ← List.append_assoc, digitsVal_zeros, List.length_append,
        List.length_replicate]
      push_cast
      have hexp : 6 - bs.length + (bs.length + z) = z + 6 := by omega
      rw [mul_assoc, ← pow_add, hexp, pow_add]
      ring
  · simp only [hs, Bool.false_eq_true, ite_false] at hrest
    obtain ⟨hdig, hval, hdec⟩ := hrest
    refine ⟨p, [], Or.inl ⟨rfl, rfl⟩, by simpa using hdig, by simpa using hex, ?_⟩
    rw [hv, hval, hdec]
    simp

/-- Given that `parse_fixed` returns `Ok v`, `s` is a decimal string whose exact value is
    `v / SCALE`. -/
theorem parse_fixed_spec (s : Slice Std.U8) :
    parse_fixed s ⦃ r => ∀ v, r = .Ok v → DecimalValue (s.val.map (·.val)) v.val ⦄ := by
  unfold parse_fixed
  step with parse_digits_spec s as ⟨ r, hr ⟩
  step as ⟨ cf, hcf ⟩
  cases r with
  | Ok val =>
    obtain ⟨value, decimals⟩ := val
    simp only at hcf
    subst hcf
    simp only
    obtain ⟨d, hd, hany, rfl, rfl⟩ := hr value decimals rfl
    have hdec6 : d.decimals.val ≤ 6 := by
      obtain ⟨-, hrest⟩ := hd
      split at hrest
      · obtain ⟨_, _, _, _, _, hb6, _, _, hdec⟩ := hrest; omega
      · omega
    have hv0 : 0 ≤ d.value.val := by
      obtain ⟨-, hrest⟩ := hd
      split at hrest
      · obtain ⟨_, _, _, _, _, _, _, hval, _⟩ := hrest; rw [hval]; positivity
      · rw [hrest.2.1]; positivity
    apply WP.spec_mono (scale_up_spec d.value d.decimals hdec6 hv0)
    intro r hr' v hv
    exact hd.decimalValue hany (hr' v hv)
  | Err e =>
    simp only at hcf
    subst hcf
    simp only
    apply WP.spec_mono (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
      _ (core.convert.FromSame Error) e e rfl)
    intro out hout v hv
    simp [hout] at hv

/-- Given that `Price::parse` returns `Ok p`, `s` is a decimal string whose exact value is
    `p / SCALE`. -/
theorem Price.parse_spec (s : Slice Std.U8) :
    Price.parse s ⦃ r => ∀ p, r = .Ok p → DecimalValue (s.val.map (·.val)) p.val ⦄ := by
  unfold Price.parse
  step with parse_fixed_spec s as ⟨ r, hr ⟩
  cases r <;> simp_all [WP.spec_ok]

/-- Given that `Quantity::parse` returns `Ok q`, `s` is a decimal string whose exact value is
    `q / SCALE`. -/
theorem Quantity.parse_spec (s : Slice Std.U8) :
    Quantity.parse s ⦃ r => ∀ q, r = .Ok q → DecimalValue (s.val.map (·.val)) q.val ⦄ := by
  unfold Quantity.parse
  step with parse_fixed_spec s as ⟨ r, hr ⟩
  cases r <;> simp_all [WP.spec_ok]

/-- A well formed string has at least one digit. -/
theorem WellFormed.exists_digit {L : List Nat} (h : WellFormed L) : ∃ c ∈ L, IsDigit c := by
  obtain ⟨a, b, hs, -, ⟨c, hc, hdc⟩, -⟩ := h
  refine ⟨c, ?_, hdc⟩
  rcases hs with ⟨rfl, rfl⟩ | rfl
  · simpa using hc
  · simp only [List.mem_append, List.mem_cons] at hc ⊢
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inr hc)

/-- Starting at `i`, the loop never fails on a well formed string. -/
theorem parse_digits_loop_ok (s : Slice Std.U8) (d : Digits) (i : Std.Usize)
    (hi : i.val ≤ s.length) (hd : DigitsInv ((s.val.take i.val).map (·.val)) d)
    (hwf : WellFormed (s.val.map (·.val))) :
    parse_digits_loop s d i ⦃ r => ∃ x, r = .Ok x ⦄ := by
  unfold parse_digits_loop
  apply loop.spec_decr_nat (fun x : Digits × Std.Usize => s.length - x.2.val)
    (fun x : Digits × Std.Usize => x.2.val ≤ s.length ∧
      DigitsInv ((s.val.take x.2.val).map (·.val)) x.1)
  · rintro ⟨d, i⟩ ⟨hi, hd⟩
    simp only at hi hd ⊢
    unfold parse_digits_loop.body
    simp only [Slice.len]
    split
    · step as ⟨ x, hx ⟩
      have hlt : i.val < (s.val.map (·.val)).length := by simp; scalar_tac
      have hok := hwf.charOk hlt (d := d) (by rw [← List.map_take]; exact hd)
      have hxv : (s.val.map (·.val))[i.val] = x.val := by simp [hx]
      rw [hxv] at hok
      step with read_char_ok_spec _ d x hd hok as ⟨ r, d', hr, hnext ⟩
      subst hr
      step as ⟨ cf, hcf ⟩
      subst hcf
      step as ⟨ i3, hi3 ⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have htake : s.val.take i3.val = s.val.take i.val ++ [x] := by
        rw [hi3, List.take_succ_eq_append_getElem (by scalar_tac), hx]
      rw [htake, List.map_append]
      simpa using hnext
    · have hlen : i.val = s.length := by scalar_tac
      have hall : s.val.take i.val = s.val := by rw [hlen]; simp
      rw [hall] at hd
      have hany : d.any_digit = true := hd.1.mpr hwf.exists_digit
      simp [hany, WP.spec_ok]
  · exact ⟨hi, hd⟩

/-- If `x * 10` is at most `n`, then `x` is at most `n / 10`. -/
theorem le_tdiv_of_mul_ten_le {x n : Int} (hn : 0 ≤ n) (h : x * 10 ≤ n) : x ≤ n.tdiv 10 := by
  rw [Int.tdiv_eq_ediv_of_nonneg hn]
  omega

/-- `scale_up` never fails when the result fits in an `I64`. -/
theorem scale_up_ok (value : Std.I64) (decimals : Std.U32) (hdec : decimals.val ≤ 6)
    (hv : 0 ≤ value.val) (hfit : value.val * 10 ^ (6 - decimals.val) ≤ I64.max) :
    scale_up value decimals ⦃ r => ∃ x, r = .Ok x ⦄ := by
  unfold scale_up scale_up_loop
  apply loop.spec_decr_nat (fun x : Std.I64 × Std.U32 => 6 - x.2.val)
    (fun x : Std.I64 × Std.U32 => x.2.val ≤ 6 ∧ 0 ≤ x.1.val ∧
      x.1.val * 10 ^ (6 - x.2.val) ≤ I64.max)
  · rintro ⟨w, k⟩ ⟨hk, hw, hfit⟩
    simp only at hk hw hfit ⊢
    unfold scale_up_loop.body
    split
    · have hmax := I64_MAX_val
      have hrmax : I64.rMax = I64.max := by simp [I64.rMax, I64.max, I64.numBits]
      step as ⟨ m, hm ⟩
      have h6 : 6 - k.val = (6 - (k.val + 1)) + 1 := by scalar_tac
      rw [h6, pow_succ] at hfit
      have hp : (1 : Int) ≤ 10 ^ (6 - (k.val + 1)) := one_le_pow₀ (by norm_num)
      have hw10 : w.val * 10 ≤ I64.rMax := by rw [hrmax]; nlinarith
      have h0 : (0 : Int) ≤ I64.rMax := by simp [I64.rMax]
      have hle := le_tdiv_of_mul_ten_le h0 hw10
      split
      · rename_i hov
        have : m.val < w.val := by scalar_tac
        rw [hm] at this
        omega
      · step as ⟨ w', hw' ⟩
        step as ⟨ k', hk' ⟩
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [hw', hk']
        nlinarith
    · simp [WP.spec_ok]
  · exact ⟨hdec, hv, hfit⟩

/-- A string has at most one exact value. -/
theorem DecimalValue.unique {L : List Nat} {v v' : Int} (h : DecimalValue L v)
    (h' : DecimalValue L v') : v = v' := by
  obtain ⟨a, b, hs, hdig, -, heq⟩ := h
  obtain ⟨a', b', hs', hdig', -, heq'⟩ := h'
  have hna : ∀ c ∈ a, c ≠ 46 := fun c hc => (hdig c (List.mem_append_left _ hc)).ne_dot
  have hna' : ∀ c ∈ a', c ≠ 46 := fun c hc => (hdig' c (List.mem_append_left _ hc)).ne_dot
  have hab : a = a' ∧ b = b' := by
    rcases hs with ⟨rfl, rfl⟩ | rfl <;> rcases hs' with ⟨h1, rfl⟩ | h1
    · exact ⟨h1, rfl⟩
    · exact absurd (hna 46 (by rw [h1]; simp)) (by simp)
    · exact absurd (hna' 46 (by rw [← h1]; simp)) (by simp)
    · exact split_at_dot hna hna' h1
  obtain ⟨rfl, rfl⟩ := hab
  have : (0 : Int) < 10 ^ b.length := by positivity
  nlinarith

/-- `parse_fixed` never fails on a decimal string whose exact value fits in an `I64`. -/
theorem parse_fixed_ok (s : Slice Std.U8) {v : Int} (hv : DecimalValue (s.val.map (·.val)) v)
    (hfit : v ≤ I64.max) :
    parse_fixed s ⦃ r => ∃ x, r = .Ok x ⦄ := by
  have hwf := hv.wellFormed hfit
  unfold parse_fixed
  have hok : parse_digits s ⦃ r => ∃ x, r = .Ok x ⦄ := by
    unfold parse_digits
    exact parse_digits_loop_ok s _ 0#usize (by simp) (by simpa using DigitsInv.nil) hwf
  have hdig := WP.spec_and (parse_digits_spec s) hok
  step with hdig as ⟨ r, hsound, x, hr ⟩
  subst hr
  obtain ⟨value, decimals⟩ := x
  step as ⟨ cf, hcf ⟩
  subst hcf
  try simp only
  obtain ⟨d, hd, hany, rfl, rfl⟩ := hsound _ _ rfl
  have hdec6 : d.decimals.val ≤ 6 := by
    obtain ⟨-, hrest⟩ := hd
    split at hrest
    · obtain ⟨_, _, _, _, _, hb6, _, _, hdec⟩ := hrest; omega
    · omega
  have hval := hd.decimalValue hany rfl
  have heq := hval.unique hv
  exact scale_up_ok d.value d.decimals hdec6 hd.value_nonneg (by rw [heq]; exact hfit)

/-- `parse_fixed` returns `Ok v` exactly when `s` is a decimal string whose exact value fits
    in an `I64`, and then that value is `v / SCALE`. -/
theorem parse_fixed_correct (s : Slice Std.U8) :
    parse_fixed s ⦃ r => match r with
      | .Ok v => DecimalValue (s.val.map (·.val)) v.val
      | .Err _ => ¬ ∃ v : Int, DecimalValue (s.val.map (·.val)) v ∧ v ≤ I64.max ⦄ := by
  by_cases hex : ∃ v : Int, DecimalValue (s.val.map (·.val)) v ∧ v ≤ I64.max
  · obtain ⟨v, hv, hfit⟩ := hex
    apply WP.spec_mono (WP.spec_and (parse_fixed_spec s) (parse_fixed_ok s hv hfit))
    rintro r ⟨h1, x, rfl⟩
    exact h1 x rfl
  · apply WP.spec_mono (parse_fixed_spec s)
    intro r h1
    cases r with
    | Ok x => exact h1 x rfl
    | Err e => exact hex

/-- `Price::parse` returns `Ok p` exactly when `s` is a decimal string whose exact value fits
    in an `I64`, and then that value is `p / SCALE`. -/
theorem Price.parse_correct (s : Slice Std.U8) :
    Price.parse s ⦃ r => match r with
      | .Ok p => DecimalValue (s.val.map (·.val)) p.val
      | .Err _ => ¬ ∃ v : Int, DecimalValue (s.val.map (·.val)) v ∧ v ≤ I64.max ⦄ := by
  unfold Price.parse
  step with parse_fixed_correct s as ⟨ r, hr ⟩
  cases r <;> simp_all [WP.spec_ok]

/-- `Quantity::parse` returns `Ok q` exactly when `s` is a decimal string whose exact value
    fits in an `I64`, and then that value is `q / SCALE`. -/
theorem Quantity.parse_correct (s : Slice Std.U8) :
    Quantity.parse s ⦃ r => match r with
      | .Ok q => DecimalValue (s.val.map (·.val)) q.val
      | .Err _ => ¬ ∃ v : Int, DecimalValue (s.val.map (·.val)) v ∧ v ≤ I64.max ⦄ := by
  unfold Quantity.parse
  step with parse_fixed_correct s as ⟨ r, hr ⟩
  cases r <;> simp_all [WP.spec_ok]

end book_core.Spec
