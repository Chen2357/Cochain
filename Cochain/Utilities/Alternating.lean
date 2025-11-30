import LieRinehart.Alternating

namespace AlternatingMap

section

variable {R : Type*}  [CommSemiring R]
variable {M : Type*} [AddCommMonoid M]  [Module R M]
variable {N : Type*}  [AddCommMonoid N] [Module R N]
variable {ι : Type*}
variable {S : Type*}  [CommSemiring S] [Algebra S R] [Module S N] [IsScalarTower S R N]

instance : IsScalarTower S R (M [⋀^ι]→ₗ[R] N) where
  smul_assoc s r f := by
    ext v
    simp

end

section

variable {n : ℕ}
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {L : Type*} [LieRing L] [LieAlgebra R L] [LieRinehartPair A L] [LieRinehartAlgebra R A L]

variable {M : Type*} [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable {N : Type*} [AddCommGroup N] [Module A N] [LieRingModule L N] [LieRinehartModule A L N]
variable [Module R N] [IsScalarTower R A N] [LieModule R L N]

instance : LieModule R L (M [⋀^(Fin n)]→ₗ[A] N) where
  lie_smul r x f := by
    ext v
    induction n
    case zero => simp
    case succ n h =>
      simp [lie_apply_succ, smul_sub]
      rw [algebra_compatible_smul A]
      simp [-algebraMap_smul]
      simp [h]
  smul_lie r x f := by
    ext v
    induction n
    case zero => simp
    case succ n h =>
      simp [lie_apply_succ, smul_sub, h]
      rw [algebra_compatible_smul A]
      simp [-algebraMap_smul]
      simp

end
