import Cochain.Basic
import LieRinehart.Alternating
import LieRinehart.Utilities.DirectSum

open DirectSum

namespace Cochain

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M]

def ι : L →ₗ[A] Cochain A L M →ₗ[A] Cochain A L M := {
  toFun x := {
    toFun := toModule A ℕ (Cochain A L M) fun
      | 0 => 0
      | i + 1 => (lof A _ (fun k => L [⋀^Fin k]→ₗ[A] M) i) ∘ₗ {
        toFun f := f.curryLeft x
        map_add' := by simp
        map_smul' := by simp
      }
    map_add' := by simp
    map_smul' m x := by
      induction x using DirectSum.induction_on
      case zero => simp
      case add => simp [*]
      case of n f => simp [←lof_eq_of A]
  }
  map_add' x y := by
    ext n f m v
    simp
    cases n
    all_goals simp [lof_eq_of]
  map_smul' a x := by
    ext n f m v
    simp
    cases n
    all_goals simp [lof_eq_of]
}

@[simp]
theorem ι_of_zero (x : L) (f : L [⋀^Fin 0]→ₗ[A] M) :
  ι x (of _ 0 f) = 0 := by simp [ι, ←lof_eq_of A]

@[simp]
theorem ι_of_succ (x : L) {n : ℕ} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) :
  ι x (of _ (n + 1) f) = of _ n (f.curryLeft x) := by simp [ι, ←lof_eq_of A]

theorem ι_apply (x : L) (f : Cochain A L M) (n : ℕ) :
  ι x f n = (f (n + 1)).curryLeft x := by
  induction f using DirectSum.induction_on
  case zero => simp
  case of m f =>
    by_cases h : m = n + 1
    . cases h
      simp
    . simp [of_eq_of_ne _ _ _ (Ne.symm h)]
      cases m
      . simp
      . simp
        simp at h
        rw [of_eq_of_ne _ _ _ (Ne.symm h)]
  case add =>
    simp [*]

theorem eq_of_ι (f g : Cochain A L M)
  (zero : f 0 = g 0)
  (succ : ∀ x : L, ι x f = ι x g) : f = g := by
  induction g using DirectSum.induction_on
  case zero =>
    ext1 i
    cases i
    case zero => exact zero
    case succ i =>
      apply AlternatingMap.eq_of_curryLeft
      intro y
      have : ι y f i = 0 := by
        simp [succ y]
      simp [ι_apply] at this
      simp [this]
  case of n g =>
    ext1 i
    cases i
    case zero => exact zero
    case succ i =>
      apply AlternatingMap.eq_of_curryLeft
      intro y
      have : ι y f i = ι y (of _ _ g) i := by
        rw [succ y]
      simp [ι_apply] at this
      rw [this]
  case add g₁ g₂ _ _ =>
    ext1 i
    cases i
    case zero => exact zero
    case succ i =>
      apply AlternatingMap.eq_of_curryLeft
      intro y
      have : ι y f i = ι y (g₁ + g₂) i := by
        rw [succ y]
      simp [ι_apply] at *
      rw [this]

variable [LieRingModule L M] [LieRinehartModule A L M]

theorem lie_ι (x : L) (y : L) (f : Cochain A L M) :
  ⁅x, ι y f⁆ = ι y (⁅x, f⁆) + ι ⁅x, y⁆ f := by
  induction f using DirectSum.induction_on
  case zero => simp
  case of n f =>
    cases n
    simp
    simp
  case add =>
    simp at *
    simp [*]
    abel

theorem ι_lie (x : L) (y : L) (f : Cochain A L M) :
  ι x (⁅y, f⁆) = ⁅y, ι x f⁆ - ι ⁅y, x⁆ f := by
  rw [lie_ι]
  abel
