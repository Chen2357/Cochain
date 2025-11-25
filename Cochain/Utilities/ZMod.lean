import Mathlib.Data.ZMod.Basic

instance : HPow ℤˣ (ZMod 2) ℤˣ where
  hPow a n := if n = 0 then 1 else a

namespace ZMod

@[elab_as_elim]
def cases₂ {motive : ZMod 2 → Sort*}
  (zero : motive 0)
  (one : motive 1)
  (n : ZMod 2) : motive n := by
  cases n using Fin.cases
  case zero => exact zero
  case succ x =>
    rw [(by apply Subsingleton.elim : x = 0)]
    exact one

@[simp]
theorem negOnePow_zero : (-1 : ℤˣ) ^ (0 : ZMod 2) = 1 := rfl

@[simp]
theorem negOnePow_one : (-1 : ℤˣ) ^ (1 : ZMod 2) = -1 := rfl

@[simp]
theorem negOnePow_mul_self (n : ZMod 2) : (-1 : ℤˣ) ^ (n * n) = (-1 : ℤˣ) ^ n := cases₂ rfl rfl n

end ZMod
