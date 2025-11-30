import Cochain.Basic
import LieRinehart.Alternating

open LieRinehartModule

namespace AlternatingMap

section

variable (A L M : Type*)
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M] [IsTrivial A L M]

private theorem smul_lie_curryLeft : ∀ (a : A) (x : L) (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (y : L),
  ⁅a • x, f.curryLeft y⁆ = a • ⁅x, f.curryLeft y⁆ + a • ⁅y, f.curryLeft x⁆ - ⁅a • y, f.curryLeft x⁆ := by
  induction n
  case zero => intros; ext; simp
  case succ n h =>
    intros a x f y
    apply eq_of_curryLeft
    intro z
    simp [←curryLeftLinearMap_apply]
    simp
    rw [curryLeft_skew f y z]
    simp [h a x]
    simp [curryLeft_skew f x z, curryLeft_skew f x y]
    apply sub_eq_zero.mp
    abel_nf
    simp
    abel

private theorem symbol_swap (x : L) (a : A) (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (y : L) :
  symbol A L _ x a (f.curryLeft y) = -symbol A L _ y a (f.curryLeft x) := by
  simp [symbol]
  rw [smul_lie_curryLeft]
  abel

private lemma vecCons_tail {n L} (x : L) (v : Fin (n + 1) → L) :
  Matrix.vecCons x (Fin.tail v) = Function.update v 0 x := by
  ext i
  cases i using Fin.cases
  case zero => rfl
  case succ i => rfl

structure DifferentialAuxSystem (n : ℕ) where
  d : (L [⋀^Fin n]→ₗ[A] M) →+ (L [⋀^Fin (n+1)]→ₗ[A] M)
  d' : (L [⋀^Fin (n-1)]→ₗ[A] M) →+ (L [⋀^Fin n]→ₗ[A] M)
  curryLeft_d : match n with
    | 0 => ∀ x f, (d f).curryLeft x = ⁅x, f⁆
    | _ + 1 => ∀ x f, (d f).curryLeft x = ⁅x, f⁆ - d' (f.curryLeft x)
  symbol_eq : ∀ a x f, symbol A L _ x a f = d (a • f.curryLeft x) - a • d (f.curryLeft x)

@[simp]
def d_aux_zero : DifferentialAuxSystem A L M 0 where
  d := {
    toFun f := {
      toFun v := ⁅v 0, f ![]⁆
      map_update_add' := by simp
      map_update_smul' := by simp
      map_eq_zero_of_eq' := by simp
    }
    map_add' := by intros; ext; simp
    map_zero' := by ext; simp
  }
  d' := 0
  curryLeft_d := by simp; intros; ext; simp
  symbol_eq := by
    intros
    ext
    simp [LieRinehartModule.symbol, lie_apply, smul_sub, lier_smul]
    congr
    ext i
    cases i using Fin.cases
    case zero => rfl
    case succ i => cases i; contradiction

@[simp]
def d_aux_succ (n : ℕ) (sys : DifferentialAuxSystem A L M n) : DifferentialAuxSystem A L M (n + 1) where
  d := {
    toFun f := uncurryLeft {
      toFun x := ⁅x, f⁆ - sys.d (f.curryLeft x)
      map_add' := by intros; ext; simp; abel
      map_smul' := by
        intros a x
        simp [smul_lier, sys.symbol_eq, smul_sub]
        abel
    } <| by
      simp
      intro
      simp [←curryLeftLinearMap_apply]
      simp
      cases n
      case zero =>
        simp [sys.curryLeft_d]
      case succ n =>
        have := sys.curryLeft_d
        simp at this
        simp [this]
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp; abel
  }
  d' := sys.d
  curryLeft_d := by
    simp
    intros
    ext
    simp [Matrix.vecCons]
  symbol_eq := by
    intros a x f
    ext v
    have tail_zero : Fin.tail v 0 = v 1 := rfl
    simp [symbol, lier_smul, lie_apply_succ, smul_sub, vecCons_tail, tail_zero]
    have := sub_eq_iff_eq_add.mp <| Eq.symm <| sys.symbol_eq a (v 0) (f.curryLeft x)
    rw [this, curryLeft_skew f (v 0) (v 1), symbol_swap]
    simp [symbol]
    have (f : L [⋀^Fin (n + 1)]→ₗ[A] M) : f (Fin.tail v) = (f.curryLeft (v 1)) (Fin.tail (Fin.tail v)) := by
      simp
      congr
      ext i
      cases i using Fin.cases
      case zero => rfl
      case succ i => rfl
    rw [this]
    simp [curryLeft_skew f (v 0) (v 1), smul_sub, lie_apply_succ, tail_zero, vecCons_tail]
    abel

@[simp]
def d_aux (n : ℕ) : DifferentialAuxSystem A L M n := by
  induction n with
  | zero => exact d_aux_zero A L M
  | succ n ih => exact d_aux_succ A L M n ih

end

section

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M] [IsTrivial A L M]

def d {n : ℕ} : (L [⋀^Fin n]→ₗ[A] M) →+ (L [⋀^Fin (n+1)]→ₗ[A] M) := (d_aux A L M n).d

@[simp]
theorem curryLeft_d_of_zero (f : L [⋀^Fin 0]→ₗ[A] M) (x : L) : (d f).curryLeft x = ⁅x, f⁆ := (d_aux A L M 0).curryLeft_d x f

@[simp]
theorem d_apply_zero (f : L [⋀^Fin 0]→ₗ[A] M) (v : Fin 1 → L) : d f v = ⁅v 0, f ![]⁆ := by
  simp [d]

@[simp]
theorem curryLeft_d_of_succ {n : ℕ} (f : L [⋀^Fin (n+1)]→ₗ[A] M) (x : L) : (d f).curryLeft x = ⁅x, f⁆ - d (f.curryLeft x) := (d_aux A L M (n+1)).curryLeft_d x f

@[simp]
theorem d_apply_succ (f : L [⋀^Fin (n+1)]→ₗ[A] M) (v : Fin (n+2) → L) : d f v = ⁅v 0, f⁆ (Fin.tail v) - d (f.curryLeft (v 0)) (Fin.tail v) := by
  simp [d]

theorem d_lie {n : ℕ} (x : L) (f : L [⋀^Fin n]→ₗ[A] M) :
  d (⁅x, f⁆) = ⁅x, d f⁆ := by
  induction n
  case zero =>
    apply eq_of_curryLeft
    intro x
    simp
  case succ n h =>
    apply eq_of_curryLeft
    intro x
    simp [h]
    abel

@[simp]
theorem d_d_apply {n : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) : d (d f) = 0 := by
  induction n with
  | zero =>
    apply eq_of_curryLeft
    intro x
    apply eq_of_curryLeft
    intro y
    simp
    simp [←curryLeftLinearMap_apply]
    simp
  | succ n h =>
    apply eq_of_curryLeft
    intro x
    apply eq_of_curryLeft
    intro y
    simp [h]
    simp [←curryLeftLinearMap_apply]
    simp [d_lie]

end

section

variable (R : Type*) {A L M : Type*}
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable [LieRinehartModule A L M] [IsTrivial A L M]

@[simp]
theorem d_smul_eq_smul_d {n : ℕ} (r : R) (f : L [⋀^Fin n]→ₗ[A] M) : d (r • f) = r • d f := by
  ext v
  induction n with
  | zero => simp
  | succ n h =>
    simp [←curryLeftLinearMap_apply, smul_sub]
    rw [h]
    simp

def dLinear {n : ℕ} : (L [⋀^Fin n]→ₗ[A] M) →ₗ[R] (L [⋀^Fin (n+1)]→ₗ[A] M) where
  toFun := d
  map_add' := by simp
  map_smul' := by simp

theorem dLinear_apply {n : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) : dLinear R f = d f := rfl

end

end AlternatingMap

open DirectSum

namespace Cochain

section

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M] [IsTrivial A L M]

def d : Cochain A L M →+ Cochain A L M := toAddMonoid fun n => AddMonoidHom.comp (of (fun k => L [⋀^Fin k]→ₗ[A] M) (n+1)) AlternatingMap.d

@[simp]
theorem d_of {n : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) :
  d (of _ n f) = of _ (n+1) (AlternatingMap.d f) := by simp [d]

@[simp]
theorem d_lof {n : ℕ} (f : L [⋀^Fin n]→ₗ[A] M) :
  d (lof A _ _ n f) = lof A _ _ (n+1) (AlternatingMap.d f) := d_of f

end

section

variable (R : Type*) {A L M : Type*}
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable [LieRinehartModule A L M] [IsTrivial A L M]

@[simp]
theorem d_smul_eq_smul_d (r : R) (x : Cochain A L M) : d (r • x) = r • d x := by
  induction x using DirectSum.induction_on
  case zero => simp
  case add => simp [*]
  case of n f =>
    simp [←lof_eq_of R]
    rw [←LinearMap.map_smul]
    rw [lof_eq_of, lof_eq_of]
    simp
    simp [←lof_eq_of R]

def dLinear : Cochain A L M →ₗ[R] Cochain A L M where
  toFun := d
  map_add' := by simp
  map_smul' := by simp

theorem dLinear_apply (x : Cochain A L M) : dLinear R x = d x := rfl

end

end Cochain
