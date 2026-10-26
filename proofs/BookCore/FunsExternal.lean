-- Hand-written models for std functions Aeneas does not provide yet.
module
public import Aeneas
public import BookCore.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

set_option maxHeartbeats 1000000

set_option maxRecDepth 2048
open book_core

/-- `Vec::remove`. Removes and returns the element at `i`, shifting the rest left.
    Fails if `i` is out of bounds. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove {T : Type _} (A : Type _) (v : alloc.vec.Vec T) (i : Std.Usize) :
    Result (T × alloc.vec.Vec T) :=
  if h : i.val < v.length then
    ok (v.val[i.val], .from (v.val.eraseIdx i.val)
      ((List.length_eraseIdx_le _ _).trans v.property))
  else
    fail .arrayOutOfBounds

/-- Given `i` in bounds, `Vec::remove` returns the element at `i` and the vector without it. -/
@[step]
theorem alloc.vec.Vec.remove_spec {T : Type _} (A : Type _) (v : alloc.vec.Vec T) (i : Std.Usize)
    (h : i.val < v.length) :
    alloc.vec.Vec.remove A v i ⦃ r => r.1 = v.val[i.val] ∧ r.2.val = v.val.eraseIdx i.val ⦄ := by
  simp [alloc.vec.Vec.remove, h]

/-- `u8::is_ascii_digit`. Whether `c` is one of the bytes `'0'` to `'9'`. -/
@[rust_fun "core::num::{u8}::is_ascii_digit"]
def core.num.U8.is_ascii_digit (c : Std.U8) : Result Bool :=
  ok (decide (48 ≤ c.val ∧ c.val ≤ 57))
