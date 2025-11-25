import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Cochain.Utilities.Parity

section GradedCommRing

variable {A ι : Type*} [Ring A] [SetLike σ A] [AddSubmonoidClass σ A]

class SuperCommRing (𝒜 : ZMod 2 → σ) extends GradedRing 𝒜 where
  super_comm {n m : ZMod 2} (x y : A) : (x ∈ 𝒜 n) → (y ∈ 𝒜 m) → x * y = (-1) ^ (n.val * m.val) * (y * x)

variable (𝒜 : ZMod 2 → σ) [SuperCommRing 𝒜]
variable {n m : ZMod 2}

theorem super_comm {x y : A} (hx : x ∈ 𝒜 n) (hy : y ∈ 𝒜 m) :
  x * y = (-1) ^ (n.val * m.val) * (y * x) :=
  SuperCommRing.super_comm x y hx hy

theorem super_comm_self {x : A} (hx : x ∈ 𝒜 n) :
  x * x = (-1) ^ n.val * (x * x) := by
  have := super_comm 𝒜 hx hx
  simp at this
  exact this

@[simp]
lemma mul_self_eq_zero_of_mem [IsAddTorsionFree A] {x : A} (hx : x ∈ 𝒜 1) : x * x = 0 := by
  have h := super_comm_self 𝒜 hx
  simp [ZMod.val_one] at h
  rw [eq_neg_iff_add_eq_zero] at h
  apply nsmul_right_injective (by norm_num : 2 ≠ 0)
  simp [two_mul, h]

end GradedCommRing

section GradedCommAlgebra

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]

abbrev SuperCommAlgebra (𝒜 : ZMod 2 → Submodule R A) := SuperCommRing 𝒜

end GradedCommAlgebra
