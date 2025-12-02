import Cochain.Interior
import Cochain.Differential
import Cochain.Algebra
import LieRinehart.Utilities.DirectSum

open DirectSum

namespace Cochain

section

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M]
variable [LieRinehartModule.IsTrivial A L M]

theorem ι_d (x : L) (f : Cochain A L M) :
  ι x (d f) = ⁅x, f⁆ - d (ι x f) := by
  induction f using DirectSum.induction_on
  case zero => simp
  case of n f =>
    cases n
    case zero => simp
    case succ => simp
  case add =>
    simp [*]
    abel

theorem lie_eq_add (x : L) (f : Cochain A L M) :
  ⁅x, f⁆ = ι x (d f) + d (ι x f) := by
  rw [ι_d]
  abel

end

section

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

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
theorem ι_of_mul (x : L) {n m : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  ι x (of _ (n + m) (AlternatingMap.mul _ _ _ f g)) =
    ι x (of _ n f) * of _ m g + (-1) ^ n * of _ n f * ι x (of _ m g) := by
  simp [←ι_mul_of]

@[simp]
theorem ι_algebraMap (x : L) (f : M) :
  ι x (algebraMap M (Cochain A L M) f) = 0 := by
  simp [algebraMap_apply]

@[simp]
theorem ι_one (x : L) : ι x (1 : Cochain A L M) = 0 := by
  simp [one_def]

variable [LieRingModule L M] [LieRinehartModule A L M] [LieRinehartModule.IsTrivial A L M]

@[simp]
theorem d_algebraMap_apply_zero (f : M) : d (algebraMap M (Cochain A L M) f) 0 = 0 := by
  simp [algebraMap_apply]
  exact of_eq_of_ne _ _ _ (by trivial)

@[simp]
theorem d_smul_one_apply_zero (f : M) :
  d (f • (1 : Cochain A L M)) 0 = 0 := by
  simp [one_def, ←lof_eq_of M]
  rw [←LinearMap.map_smul, lof_eq_of]
  simp
  rw [of_eq_of_ne _ _ _ (by trivial)]

@[simp]
theorem d_algebraMap_apply_one_apply (f : M) (v : Fin 1 → L) : d (algebraMap M (Cochain A L M) f) 1 v = ⁅v 0, f⁆ := by
  simp [algebraMap_apply]

@[simp]
theorem d_smul_one_apply_one_apply (f : M) (v : Fin 1 → L) :
  d (f • (1 : Cochain A L M)) 1 v = ⁅v 0, f⁆ := by
  simp [one_def, ←lof_eq_of M]
  rw [←LinearMap.map_smul, lof_eq_of]
  simp

@[simp]
theorem d_algebraMap_apply_ne (f : M) (n : ℕ) (hn : n ≠ 1) : d (algebraMap M (Cochain A L M) f) n = 0 := by
  simp [algebraMap_apply]
  rw [of_eq_of_ne _ _ _ hn]

@[simp]
theorem d_smul_one_apply_ne (f : M) (n : ℕ) (hn : n ≠ 1) :
  d (f • (1 : Cochain A L M)) n = 0 := by
  simp [one_def, ←lof_eq_of M]
  rw [←LinearMap.map_smul, lof_eq_of]
  simp
  rw [of_eq_of_ne _ _ _ hn]

end

end Cochain

section

namespace AlternatingMap

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]

section

variable [CommRing M] [Algebra A M]
variable [LieRinehartRing L M] [LieRinehartModule A L M]

theorem lie_mul {n m l : ℕ} (x : L) : ∀ (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M), ⁅x, mul n m l f g⁆ = mul _ _ _ (⁅x, f⁆) g + mul _ _ _ f (⁅x, g⁆) := by
  by_cases hnm : n + m = l
  case neg =>
    simp [mul_of_ne _ _ _ hnm]
  case pos =>
  cases hnm
  case refl =>
  induction n, m using Nat.pincerRecursion
  case Ha0 m =>
    intros
    ext
    simp [lie_apply, mul_sub, Finset.mul_sum]
    abel
  case H0b n =>
    have : 0 + n = n := by linarith
    rw [this]
    intros
    ext
    simp [lie_apply, mul_sub, Finset.mul_sum]
    abel
  case H n m hn hm =>
    intros f g
    apply eq_of_curryLeft
    intro y
    simp at *
    have : n + (m + 1) = n + 1 + m := by linarith
    apply this.recOn (motive := fun t _ => ⁅x, (((mul (n + 1) (m + 1) (t + 1)) f) g).curryLeft y⁆ -
    (((mul (n + 1) (m + 1) (t + 1)) f) g).curryLeft ⁅x, y⁆ = (((mul (n + 1) (m + 1) (t + 1)) ⁅x, f⁆) g).curryLeft y +
    (((mul (n + 1) (m + 1) (t + 1)) f) ⁅x, g⁆).curryLeft y)
    simp
    rw [hn]
    have : n + 1 + m = n + (m + 1) := by linarith
    rw [this] at hm
    rw [hm]
    simp [smul_sub]
    abel

end

section
-- There is an opportunity for generalization, but we need a class about compatibility of LieRinehartPairs
-- variable [CommRing M] [Algebra A M]
-- variable [LieRinehartPair M L] [LieRinehartModule A L M]

variable [LieRinehartModule.IsTrivial A L A]

theorem d_smul {n : ℕ} (x : A) (f : L [⋀^Fin n]→ₗ[A] A) : d (x • f) = x • d f + mul _ _ (n+1) (d (constOfIsEmpty A L (Fin 0) x)) f := by
  induction n
  case zero =>
    ext
    simp
    ring
  case succ n ih =>
    apply eq_of_curryLeft
    intro y
    simp [ih, smul_sub, lier_smul]
    abel

theorem d_mul {n m l : ℕ} (f : L [⋀^Fin n]→ₗ[A] A) (g : L [⋀^Fin m]→ₗ[A] A) : d (mul _ _ l f g) = mul _ _ _ (d f) g + (-1) ^ n • mul _ _ _ f (d g) := by
  by_cases hnm : n + m = l
  case neg =>
    have h₁: (n + 1) + m ≠ l + 1 := by intro h; simp [Nat.succ_add] at h; exact hnm h
    have h₂: n + (m + 1) ≠ l + 1 := by intro h; rw [Nat.add_succ] at h; simp at h; exact hnm h
    simp [mul_of_ne _ _ _ hnm, mul_of_ne _ _ _ h₁, mul_of_ne _ _ _ h₂]
  case pos =>
  cases hnm
  case refl =>
  induction n, m using Nat.pincerRecursion
  case Ha0 n =>
    ext v
    simp [d_smul]
    rw [mul_graded_comm]
    simp
    congr
  case H0b m =>
    have : 0 + m = m := by linarith
    rw [this]
    simp [d_smul]
    rw [add_comm (f ![] • d g)]
    congr
  case H n m hn hm =>
    simp at *
    apply eq_of_curryLeft
    intro y
    have : n + 1 + (m + 1) = n + m + 2 := by linarith
    rw [this]
    simp [lie_mul]
    have : n + (m + 1) = n + m + 1 := by linarith
    rw [this] at hn
    rw [hn]
    have : n + 1 + m = n + m + 1 := by linarith
    rw [this] at hm
    rw [hm]
    simp [←curryLeftLinearMap_apply]
    simp [smul_sub, smul_smul, ←mul_pow, pow_succ]
    abel

end

end AlternatingMap

namespace Cochain

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

variable [LieRinehartRing L M] [LieRinehartModule A L M]

instance : LieRinehartRing L (Cochain A L M) where
  lier_one x := by
    simp [one_def]
    ext i v
    cases i
    case zero => simp
    case succ n => simp [of_eq_of_ne]
  lier_mul x f g := by
    induction f using DirectSum.induction_on with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ => simp [add_mul, hf₁, hf₂]; abel
    | of n f =>
      induction g using DirectSum.induction_on with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ => simp [mul_add, hg₁, hg₂]; abel
      | of m g =>
        simp
        rw [AlternatingMap.lie_mul x f g]
        rw [map_add]
        abel

variable [LieRinehartModule.IsTrivial A L M]

@[simp]
theorem d_one : d 1 = (0 : Cochain A L M) := by
  ext i v
  by_cases h : i = 1
  . cases h
    simp [one_def]
  . simp [one_def, of_eq_of_ne _ _ _ h]

end Cochain

end
