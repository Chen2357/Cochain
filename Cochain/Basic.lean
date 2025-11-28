import LieRinehart.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Algebra.Group.TransferInstance

open DirectSum
open AlternatingMap
open Function

abbrev Cochain (A L M : Type*) [CommRing A] [LieRing L] [LieRinehartPair A L] [AddCommGroup M] [Module A M]  := DirectSum ℕ (fun n => L [⋀^Fin n]→ₗ[A] M)

namespace Cochain

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

def ofIsEmptyLinear : M ≃ₗ[M] L [⋀^Fin 0]→ₗ[A] M := {
  toFun x := constOfIsEmpty A L (Fin 0) x
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  invFun f := f ![]
  right_inv := by intro; ext; simp; congr; apply Subsingleton.elim
}

instance : Mul (L [⋀^Fin 0]→ₗ[A] M) := ofIsEmptyLinear.symm.toEquiv.mul
instance : One (L [⋀^Fin 0]→ₗ[A] M) := ofIsEmptyLinear.symm.one

@[simp]
theorem mul_apply (f g : L [⋀^Fin 0]→ₗ[A] M) : (f * g) ![] = f ![] * g ![] := rfl

@[simp]
theorem one_apply : (1 : L [⋀^Fin 0]→ₗ[A] M) ![] = 1 := rfl

instance : CommSemiring (L [⋀^Fin 0]→ₗ[A] M) where
  left_distrib := by intros; ext; simp [ofIsEmptyLinear.symm.mul_def, mul_add]
  right_distrib := by intros; ext; simp [ofIsEmptyLinear.symm.mul_def, add_mul]
  zero_mul := by intros; ext; simp [ofIsEmptyLinear.symm.mul_def, zero_mul]
  mul_zero := by intros; ext; simp [ofIsEmptyLinear.symm.mul_def, mul_zero]
  mul_assoc := ofIsEmptyLinear.symm.commMonoid.mul_assoc
  one_mul := ofIsEmptyLinear.symm.commMonoid.one_mul
  mul_one := ofIsEmptyLinear.symm.commMonoid.mul_one
  mul_comm := ofIsEmptyLinear.symm.commMonoid.mul_comm

instance : Algebra M (L [⋀^Fin 0]→ₗ[A] M) where
  algebraMap := {
    toFun := ofIsEmptyLinear
    map_one' := rfl
    map_mul' := by intros; rfl
    map_zero' := by rfl
    map_add' := by intros; rfl
  }
  commutes' := by intros; rw [mul_comm]
  smul_def' := by
    intros r x
    ext v
    show r • x v = ofIsEmptyLinear (r * (ofIsEmptyLinear.symm x)) v
    simp [ofIsEmptyLinear]
    congr
    apply Subsingleton.elim

def ofIsEmpty : M ≃ₐ[M] L [⋀^Fin 0]→ₗ[A] M := ofIsEmptyLinear.algEquivOfRing

instance : IsScalarTower A M (L [⋀^Fin n]→ₗ[A] M) where
  smul_assoc := by
    intros r s f
    ext v
    simp [←algebraMap_smul (R:=A) (A:=M)]
    ring

@[simp]
theorem curryLeft_smul {n : ℕ} (m : M) (f : L [⋀^Fin n.succ]→ₗ[A] M) (x : L) : (m • f).curryLeft x = m • (f.curryLeft x) := rfl

end Cochain
