import Cochain.Algebra

open DirectSum

namespace Cochain

section AddMonoidHom

def ι {A L M : Type*}
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] (x : L) :
  Cochain A L M →+ Cochain A L M := toAddMonoid fun
  | 0 => 0
  | i + 1 => AddMonoidHom.comp (of (fun k => L [⋀^Fin k]→ₗ[A] M) i) <| {
    toFun f := f.curryLeft x
    map_zero' := rfl
    map_add' := by simp
  }

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M]

@[simp]
theorem ι_of_zero (x : L) (f : L [⋀^Fin 0]→ₗ[A] M) :
  ι x (of _ 0 f) = 0 := by simp [ι]

@[simp]
theorem ι_of_succ (x : L) {n : ℕ} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) :
  ι x (of _ (n + 1) f) = of _ n (f.curryLeft x) := by simp [ι]

end AddMonoidHom

section LinearMap

def ιLinear {A L M : Type*}
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [CommRing M] [Algebra A M] (x : L) :
  Cochain A L M →ₗ[M] Cochain A L M := {
    toFun := ι x
    map_add' := by simp
    map_smul' m x := by
      induction x using DirectSum.induction_on
      case zero => simp
      case add => simp [*]
      case of n f =>
        simp [←lof_eq_of M]
        rw [←LinearMap.map_smul]
        rw [lof_eq_of, lof_eq_of]
        cases n
        case zero => simp
        case succ n =>
          simp
          simp [←lof_eq_of M]
  }

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

theorem ιLinear_eq_ι (x : L) (f : Cochain A L M) : ιLinear x f = ι x f := rfl

@[simp]
theorem ιLinear_of_zero (x : L) (f : L [⋀^Fin 0]→ₗ[A] M) :
  ιLinear x (of _ 0 f) = 0 := by simp [ιLinear_eq_ι]

@[simp]
theorem ιLinear_of_succ (x : L) {n : ℕ} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) :
  ιLinear x (of _ (n + 1) f) = of _ n (f.curryLeft x) := by simp [ιLinear_eq_ι]


@[simp]
theorem ι_mul_of (x : L) {n m : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  ι x (of _ n f * of _ m g) = ι x (of _ n f) * of _ m g + (-1) ^ n * of _ n f * ι x (of _ m g) := by
  cases n
  case zero =>
    simp
    cases m
    case zero =>
      simp
    case succ m =>
      simp
      rw [(by rfl : 0 + (m + 1) = 0 + m + 1)]
      simp
  case succ n =>
    cases m
    case zero =>
      simp
    case succ m =>
      simp
      rw [(by rfl : n + 1 + (m + 1) = n + 1 + m + 1)]
      simp
      congr 1
      have : n + 1 + m = n + (m + 1) := by linarith
      rw [this]
      rw [mul_assoc]
      simp

@[simp]
theorem ιLinear_mul_of (x : L) {n m : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  ιLinear x (lof M ℕ _ n f * lof M ℕ _ m g) = ιLinear x (lof M ℕ _ n f) * lof M ℕ _ m g + (-1) ^ n * lof M ℕ _ n f * ιLinear x (lof M ℕ _ m g) := ι_mul_of x f g

end LinearMap

end Cochain
