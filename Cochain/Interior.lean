import Cochain.Algebra

open DirectSum

namespace Cochain

def ι (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [CommRing M] [Algebra A M] (x : L) :
  Cochain A L M →ₗ[M] Cochain A L M := toModule M ℕ _ fun
  | 0 => 0
  | i + 1 => lof M ℕ (fun k => L [⋀^Fin k]→ₗ[A] M) i ∘ₗ {
    toFun f := f.curryLeft x
    map_add' := by simp
    map_smul' := by simp
  }

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [CommRing M] [Algebra A M]

@[simp]
theorem ι_of_zero (x : L) (f : L [⋀^Fin 0]→ₗ[A] M) :
  ι A L M x (of _ 0 f) = 0 := by simp [ι, ←lof_eq_of M]

@[simp]
theorem ι_of_succ (x : L) {n : ℕ} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) :
  ι A L M x (of _ (n + 1) f) = of _ n (f.curryLeft x) := by simp [ι, ←lof_eq_of M]

@[simp]
theorem ι_mul_of (x : L) {n m : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  ι A L M x (of _ n f * of _ m g) = ι A L M x (of _ n f) * of _ m g + (-1) ^ n * of _ n f * ι A L M x (of _ m g) := by
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

end Cochain
