import Cochain.Basic
import Mathlib.Algebra.DirectSum.Decomposition

open DirectSum

namespace Cochain

section homogeneous

def homogeneous (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [CommRing M] [Algebra A M] (n : ℕ) : Submodule M (Cochain A L M) := LinearMap.range (lof M ℕ (fun k => L [⋀^Fin k]→ₗ[A] M) n)

variable {A L M : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [CommRing M] [Algebra A M]

theorem homogeneous_mem_iff {n : ℕ} {x : Cochain A L M} :
  x ∈ homogeneous A L M n ↔ ∀ m ≠ n, x m = 0 := by
  constructor
  · intro h
    rcases h with ⟨x, rfl⟩
    intros m h
    simp [lof_eq_of, of_eq_of_ne _ _ _ h]
  · intro h
    use x n
    ext1 m
    by_cases hm : m = n
    . rw [hm, lof_eq_of, of_eq_same]
    . rw [h m hm, lof_eq_of, of_eq_of_ne _ _ _ hm]

@[simp]
theorem homogeneous_lof_mem {n : ℕ} (x : L [⋀^Fin n]→ₗ[A] M) : lof M _ _ n x ∈ homogeneous A L M n := ⟨x, rfl⟩

@[simp]
theorem homogeneous_of_mem {n : ℕ} (x : L [⋀^Fin n]→ₗ[A] M) : of _ n x ∈ homogeneous A L M n := ⟨x, rfl⟩

@[simp]
theorem homogeneous_of_mem_iff {n m : ℕ} (x : L [⋀^Fin n]→ₗ[A] M) :
  of _ n x ∈ homogeneous A L M m ↔ n = m ∨ x = 0 := by
  constructor
  · intro h
    rcases h with ⟨y, h⟩
    apply Classical.or_iff_not_imp_left.mpr
    intro hnm
    simp [lof_eq_of] at h
    have : (of (fun k => L [⋀^Fin k]→ₗ[A] M) m) y n = x := by simp [h]
    simp [of_eq_of_ne _ _ _ hnm] at this
    rw [this]
  · intro h
    cases h
    case inl h =>
      rw [←h]
      simp
    case inr h =>
      simp [h]

instance : DirectSum.Decomposition (homogeneous A L M) where
  decompose' := DirectSum.map fun n => {
    toFun x := ⟨of _ n x, ⟨x, rfl⟩⟩
    map_zero' := by simp
    map_add' := by simp [←lof_eq_of M]
  }
  left_inv x := by
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x => simp
    case add x1 x2 ih1 ih2 => simp [*]
  right_inv x := by
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x =>
      ext1 i
      ext1
      ext1 j
      simp
      by_cases h : i = n
      . rw [h, of_eq_same]
        by_cases hv : j = n
        . rw [hv, of_eq_same]
        . rw [of_eq_of_ne _ _ _ hv, homogeneous_mem_iff.mp x.2 j hv]
      . rw [of_eq_of_ne _ _ _ h, homogeneous_mem_iff.mp x.2 i h, map_zero]
        rfl
    case add x1 x2 ih1 ih2 => simp [*]

end homogeneous

section evenOdd

def evenOdd (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [CommRing M] [Algebra A M]
  (n : ZMod 2) : Submodule M (Cochain A L M) := LinearMap.range <| lmap (fun (k : ℕ) => if k = n then LinearMap.id else 0)

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [CommRing M] [Algebra A M]

@[simp]
theorem evenOdd_of_mem {n : ℕ} (x : L [⋀^Fin n]→ₗ[A] M) : of _ n x ∈ evenOdd A L M n := ⟨of _ n x, by simp⟩

@[simp]
theorem evenOdd_lof_mem {n : ℕ} (x : L [⋀^Fin n]→ₗ[A] M) : lof M _ _ n x ∈ evenOdd A L M n := evenOdd_of_mem x

@[simp]
theorem evenOdd_of_mem_iff {n : ℕ} {m : ZMod 2} {x : L [⋀^Fin n]→ₗ[A] M} :
  of _ n x ∈ evenOdd A L M m ↔ n = m ∨ x = 0 := by
  constructor
  . intro h
    rcases h with ⟨y, h⟩
    apply Classical.or_iff_not_imp_left.mpr
    have h : (lmap fun (k : ℕ) => if k = m then LinearMap.id (R:=M) else 0) y n = (of (fun i => L [⋀^Fin i]→ₗ[A] M) n) x n := by rw [h]
    intro hnm
    simp [hnm] at h
    rw [h]
  . intro h
    cases h
    case inl h =>
      rw [←h]
      simp
    case inr h =>
      simp [h]

instance : DirectSum.Decomposition (evenOdd A L M) where
  decompose' := DirectSum.toAddMonoid fun (i : ℕ) => {
    toFun x := lof M _ (fun k => evenOdd A L M k) i <| (lof M ℕ _ i).codRestrict _ (by simp) x
    map_zero' := by simp
    map_add' := by simp
  }
  left_inv x := by
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x => simp [lof_eq_of]
    case add x1 x2 ih1 ih2 => simp [*]
  right_inv x := by
    induction x using DirectSum.induction_on
    case zero => simp
    case of n x =>
      rcases x with ⟨_, ⟨x, rfl⟩⟩
      induction x using DirectSum.induction_on
      case zero =>
        simp
        conv_rhs =>
          enter [2]
          equals 0 => rfl
        simp
      case of m x =>
        simp [lof_eq_of]
        by_cases h : m = n
        . cases h
          ext1 i
          by_cases hi : i = m
          . rw [hi]
            simp
            ext
            simp [lof_eq_of]
          . simp [of_eq_of_ne _ _ _ hi]
        . simp [h]
          conv_rhs =>
            enter [2]
            equals 0 => rfl
          simp
      case add x1 x2 ih1 ih2 =>
        simp at *
        simp [*]
        conv_rhs =>
          enter [2]
          equals ⟨(lmap fun (k : ℕ) => if k = n then LinearMap.id else 0) x1, ⟨x1, rfl⟩⟩ + ⟨(lmap fun (k : ℕ) => if k = n then LinearMap.id else 0) x2, ⟨x2, rfl⟩⟩ =>
            rfl
        simp
    case add x1 x2 ih1 ih2 => simp [*]

end evenOdd

end Cochain
