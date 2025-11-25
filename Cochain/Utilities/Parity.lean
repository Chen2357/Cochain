import Mathlib.Algebra.Ring.Parity

@[simp]
theorem neg_one_pow_mul_self {R : Type*} [Monoid R]  [HasDistribNeg R] (n : ℕ) : (-1 : R) ^ (n * n) = (-1 : R) ^ n := by
  by_cases h : Even n
  · simp [h]
  · simp at h
    simp [h]
