import Cochain.Mul
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.DirectSum.Algebra
import LieRinehart.Utilities.DirectSum

namespace Cochain

open DirectSum
open AlternatingMap
open Function

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

instance : GNonUnitalNonAssocSemiring (fun n => L [⋀^Fin n]→ₗ[A] M) where
  mul f g := AlternatingMap.mul _ _ _ f g
  mul_zero := by simp
  zero_mul := by simp
  mul_add := by simp
  add_mul := by simp

instance : GradedMonoid.GOne (fun n => L [⋀^Fin n]→ₗ[A] M) where
  one := constOfIsEmpty A L (Fin 0) 1

instance : GSemiring (fun n => L [⋀^Fin n]→ₗ[A] M) where
  mul_one a := by apply Sigma.ext; simp; simp [GradedMonoid.GOne.one, GradedMonoid.GMul.mul]
  one_mul a := by
    apply Sigma.ext
    simp
    induction a
    rename_i n f
    simp
    have : n = 0 + n := by linarith
    revert f
    apply Eq.ndrec (motive := fun t => ∀ f, ((AlternatingMap.mul 0 n t) (constOfIsEmpty A L (Fin 0) 1)) f ≍ f) ?_ this
    simp
  mul_assoc a b c := by
    rcases a with ⟨n, f⟩
    rcases b with ⟨m, g⟩
    rcases c with ⟨l, h⟩
    apply Sigma.ext
    simp
    linarith
    simp [GradedMonoid.GMul.mul]
    rw [AlternatingMap.mul_assoc f g h]
    have : (n + m) + l = n + (m + l) := by linarith
    rw [this]
  natCast n := constOfIsEmpty A L (Fin 0) n
  natCast_zero := by ext; simp
  natCast_succ n := by ext; simp [GradedMonoid.GOne.one]

instance : Ring (Cochain A L M) where

@[simp]
theorem mul_lof {n m} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  (lof M _ _ _ f: Cochain A L M) * (lof M _ _ _ g : Cochain A L M) = lof M _ _ (n + m) (AlternatingMap.mul _ _ _ f g) := by
    ext1 i
    simp [lof_eq_of, HMul.hMul, Mul.mul, GradedMonoid.GMul.mul]

@[simp]
theorem mul_of {n m} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  (of _ _ f : Cochain A L M) * (of _ _ g : Cochain A L M) = of _ (n + m) (AlternatingMap.mul _ _ _ f g) :=
  mul_lof f g

@[simp]
theorem mul_apply_zero (f g : Cochain A L M) :
  (f * g) 0 = AlternatingMap.mul 0 0 0 (f 0) (g 0) := by
  induction f using DirectSum.induction_on
  case zero => simp
  case of n f =>
    induction g using DirectSum.induction_on
    case zero => simp
    case of m g =>
      simp [←lof_eq_of M]
      cases n
      case zero =>
        cases m
        simp
        rw [lof_eq_of, DirectSum.smul_apply]
        simp
        rw [lof_eq_of, of_eq_of_ne]
        nth_rw 2 [lof_eq_of]
        rw [of_eq_of_ne]
        all_goals simp
      case succ n =>
        rw [lof_eq_of, of_eq_of_ne]
        rw [lof_eq_of, of_eq_of_ne]
        all_goals try simp
        rw [add_comm, ←add_assoc]
        apply Nat.zero_ne_add_one
    case add => rw [mul_add]; simp [*]
  case add => rw [add_mul]; simp [*]

theorem one_def : (1 : Cochain A L M) = of _ 0 (constOfIsEmpty A L (Fin 0) 1) := rfl

@[simp]
theorem one_apply_zero : (1 : Cochain A L M) 0 = constOfIsEmpty A L (Fin 0) 1 := rfl

@[simp]
theorem one_apply_succ (n : ℕ) : (1 : Cochain A L M) (n + 1) = 0 := rfl

@[simp]
theorem one_apply_ne_zero (n : ℕ) (hn : n ≠ 0) : (1 : Cochain A L M) n = 0 := by
  rw [one_def]
  rw [of_eq_of_ne _ _ _ hn]

instance : GAlgebra M (fun n => L [⋀^Fin n]→ₗ[A] M) where
  toFun := {
    toFun x := constOfIsEmpty A L (Fin 0) x
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp
  }
  map_one := rfl
  map_mul := by intros; rfl
  commutes r x := by
    rcases x with ⟨n, f⟩
    apply Sigma.ext
    . simp
      apply add_comm
    . simp [GradedMonoid.GMul.mul, GradedMonoid.mk]
      have : n = 0 + n := by linarith
      revert f
      apply Eq.ndrec (motive := fun t => ∀ f, (AlternatingMap.mul 0 n t) (constOfIsEmpty A L (Fin 0) r) f ≍ r • f) ?_ this
      simp
  smul_def r x := by
    rcases x with ⟨n, f⟩
    apply Sigma.ext
    . simp [GradedMonoid.mk]
    . simp [GradedMonoid.GMul.mul, GradedMonoid.mk]
      have : n = 0 + n := by linarith
      revert f
      apply Eq.ndrec (motive := fun t => ∀ f, r • f ≍ (AlternatingMap.mul 0 n t) (constOfIsEmpty A L (Fin 0) r) f) ?_ this
      simp

theorem algebraMap_apply (r : M) : algebraMap M (Cochain A L M) r = of _ 0 (constOfIsEmpty A L (Fin 0) r) := rfl

@[simp]
theorem algebraMap_apply_zero_apply (r : M) (v : Fin 0 → L) : algebraMap M (Cochain A L M) r 0 v = r := rfl

@[simp]
theorem algebraMap_apply_succ (r : M) (n : ℕ) : algebraMap M (Cochain A L M) r (n + 1) = 0 := rfl

@[simp]
theorem algebraMap_apply_ne_zero (r : M) (n : ℕ) (hn : n ≠ 0) : algebraMap M (Cochain A L M) r n = 0 := by
  rw [algebraMap_apply]
  rw [of_eq_of_ne _ _ _ hn]

variable [LieRingModule L M] [LieRinehartModule A L M]

@[simp]
theorem lie_algebraMap (x : L) (f : M) : ⁅x, algebraMap M (Cochain A L M) f⁆ = algebraMap M (Cochain A L M) ⁅x, f⁆ := by
  ext i v
  cases i
  case zero => simp
  case succ i => simp

@[simp]
theorem lie_smul_one (x : L) (f : M) : ⁅x, f • (1 : Cochain A L M)⁆ = ⁅x, f⁆ • 1 := by
  ext i v
  cases i
  case zero => simp [DirectSum.smul_apply]
  case succ i => simp [DirectSum.smul_apply]

end Cochain

section LieRinehartAlgebra

variable (R A L M : Type*)
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [CommRing M] [Algebra A M]
variable [Algebra R M] [IsScalarTower R A M]

instance : Algebra R (Cochain A L M) := Algebra.compHom (Cochain A L M) (algebraMap R M)

instance : SMulCommClass R M (Cochain A L M) where
  smul_comm r s x := by
    show (algebraMap R M r) • (s • x) = s • ((algebraMap R M r) • x)
    rw [smul_smul, mul_comm, ←smul_smul]

instance : IsScalarTower R M (Cochain A L M) where
  smul_assoc c x y := by
    show (c • x) • y = (algebraMap R M c) • (x • y)
    simp [Algebra.smul_def]
    rw [_root_.mul_assoc]

end LieRinehartAlgebra
