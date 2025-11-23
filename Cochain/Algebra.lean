import Cochain.Mul
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Group.TransferInstance

section Cochain

open DirectSum
open AlternatingMap
open Function
open Cochain

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [CommRing M] [Algebra A M]

instance : Mul (Cochain A L M) where
  mul f g := (toModule M ℕ (Cochain A L M →ₗ[M] Cochain A L M) <| fun i => {
    toFun f := toModule M ℕ (Cochain A L M) <| fun j => (lof M ℕ (fun k => L [⋀^Fin k]→ₗ[A] M) (i + j)) ∘ₗ AlternatingMap.mul i j (i + j) f
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp
  }) f g

@[simp]
def mul_lof {n m} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  (lof M _ _ _ f: Cochain A L M) * (lof M _ _ _ g : Cochain A L M) = lof M _ _ (n + m) (AlternatingMap.mul _ _ _ f g) := by
    ext
    simp [Mul.mul, HMul.hMul]

@[simp]
def mul_of {n m} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  (of _ _ f : Cochain A L M) * (of _ _ g : Cochain A L M) = of _ (n + m) (AlternatingMap.mul _ _ _ f g) :=
  mul_lof f g

instance : Distrib (Cochain A L M) where
  left_distrib := by simp [Mul.mul, HMul.hMul]
  right_distrib := by simp [Mul.mul, HMul.hMul]

instance : MulZeroClass (Cochain A L M) where
  zero_mul f := by
    have : (0 : Cochain A L M) = of _ 0 0 := by
      ext
      simp
    induction f using DirectSum.induction_on
    case zero =>
      rw [this, mul_of]
      simp
    case add => simp [mul_add, *, -this]
    case of n f => rw [this, mul_of]; simp
  mul_zero f := by
    have : (0 : Cochain A L M) = of _ 0 0 := by
      ext
      simp
    induction f using DirectSum.induction_on
    case zero =>
      rw [this, mul_of]
      simp
    case add => simp [add_mul, *, -this]
    case of n f => rw [this, mul_of]; simp

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

instance : NonUnitalSemiring (Cochain A L M) where
  mul_assoc f g h := by
    induction f using DirectSum.induction_on
    case zero => rfl
    case add => simp [add_mul, *]
    case of n f =>
      induction g using DirectSum.induction_on
      case zero => simp
      case add => simp [add_mul, mul_add, *]
      case of m g =>
        induction h using DirectSum.induction_on
        case zero => simp
        case add h₁ h₂ ih₁ ih₂ =>
          simp [mul_add, ←ih₁, ←ih₂]
        case of l h =>
          simp
          rw [AlternatingMap.mul_assoc f g h]
          have : n + m + l = n + (m + l) := by linarith
          rw [this]

instance : One (Cochain A L M) where
  one := of _ 0 (constOfIsEmpty A L (Fin 0) 1)

theorem one_def : (1 : Cochain A L M) = of _ 0 (constOfIsEmpty A L (Fin 0) 1) := rfl

instance : Semiring (Cochain A L M) where
  one_mul f := by
    induction f using DirectSum.induction_on
    case zero => exact mul_zero 1
    case add => simp [mul_add, *]
    case of n f =>
      ext m v
      simp [one_def]
      have : 0 + n = n := by linarith
      rw [this]
      simp
  mul_one f := by
    induction f using DirectSum.induction_on
    case zero => rfl
    case add => simp [add_mul, *]
    case of n f =>
      simp [one_def]

instance : Algebra M (Cochain A L M) where
  algebraMap := {
    toFun := fun r => lof M ℕ (fun k => L [⋀^Fin k]→ₗ[A] M) 0 (constOfIsEmpty A L (Fin 0) r)
    map_one' := by simp [lof_eq_of, one_def]
    map_mul' := by
      intros
      ext i v
      simp
      cases i
      . simp
        rw [lof_eq_of, DirectSum.smul_apply]
        simp
      . rw [lof_eq_of, of_eq_of_ne, DirectSum.smul_apply, lof_eq_of, of_eq_of_ne]
        all_goals simp
    map_zero' := by
      ext i v
      cases i
      . simp
      . rw [lof_eq_of, of_eq_of_ne]
        all_goals simp
    map_add' := by
      intros
      ext i v
      cases i
      . simp
      . rw [DirectSum.add_apply]
        rw [lof_eq_of, of_eq_of_ne]
        rw [lof_eq_of, of_eq_of_ne]
        rw [lof_eq_of, of_eq_of_ne]
        all_goals simp
  }
  commutes' := by
    intros r x
    simp
    induction x using DirectSum.induction_on
    case zero => simp
    case add => simp [mul_add, *, add_mul]
    case of n f =>
      rw [lof_eq_of]
      simp
      rw [(by apply zero_add : 0 + n = n)]
      simp
  smul_def' := by
    intros r f
    ext n v
    simp
    induction f using DirectSum.induction_on
    case zero => simp
    case of k f =>
      simp [←lof_eq_of M]
      have : 0 + k = k := by linarith
      rw [this]
      simp
    case add => simp [mul_add, *]

end Cochain
