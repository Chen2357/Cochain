import Cochain.Algebra
import Cochain.Decomposition
import Mathlib.RingTheory.GradedAlgebra.Basic
import Cochain.Utilities.SuperCommAlgebra

open DirectSum

namespace Cochain

variable {A L M : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [CommRing M] [Algebra A M]

instance : GradedAlgebra (homogeneous A L M) where
  one_mem := by simp [one_def]
  mul_mem i j x y hx hy := by
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    simp

instance : GradedAlgebra (evenOdd A L M) where
  one_mem := by simp [one_def]
  mul_mem i j x y hx hy := by
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x =>
      induction y using DirectSum.induction_on
      case zero => simp
      case of m y =>
        simp at *
        by_cases hn : n = i
        . by_cases hm : m = j
          . simp [hn, hm]
          . simp [hm]
        . simp [hn]
      case add y1 y2 ih1 ih2 =>
        simp [mul_add]
        apply Submodule.add_mem
        convert ih1
        simp
        convert ih2
        simp
    case add x1 x2 ih1 ih2 =>
      simp [add_mul]
      apply Submodule.add_mem
      exact ih1
      exact ih2

instance : SuperCommAlgebra (evenOdd A L M) where
  super_comm {i j} x y hx hy := by
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x =>
      induction y using DirectSum.induction_on
      case zero => simp
      case of m y =>
        simp
        by_cases hn : n = i
        . by_cases hm : m = j
          . simp [←hn, ←hm]
            rw [AlternatingMap.mul_graded_comm]
            have (y : Cochain A L M) : (-1 : ℤˣ) ^ ((n : ZMod 2) * m) • y = (-1 : ℤ) ^ (n * m) • y := by
              norm_cast
            simp [this, zsmul_eq_mul]
            have : n + m = m + n := add_comm n m
            rw [this]
            have : n * m = m * n := mul_comm n m
            rw [this]
          . simp [hm]
        . simp [hn]
      case add y1 y2 ih1 ih2 =>
        simp at *
        simp [mul_add, add_mul, *]
    case add x1 x2 ih1 ih2 =>
        simp at *
        simp [mul_add, add_mul, *]

end Cochain
