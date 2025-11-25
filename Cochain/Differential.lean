import LieRinehart.Alternating

open AlternatingMap

namespace Cochain

section

variable (A L M : Type*)
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LRModule A L M] [LRModule.IsTrivial A L M]

structure DifferentialAuxSystem (n : ℕ) where
  d : (L [⋀^Fin n]→ₗ[A] M) →+ (L [⋀^Fin (n+1)]→ₗ[A] M)
  d' : (L [⋀^Fin (n-1)]→ₗ[A] M) →+ (L [⋀^Fin n]→ₗ[A] M)
  curryLeft_d : match n with
    | 0 => ∀ x f, (d f).curryLeft x = ⁅x, f⁆
    | _ + 1 => ∀ x f, (d f).curryLeft x = ⁅x, f⁆ - d' (f.curryLeft x)
  contr_eq : ∀ a x f, contr A L _ (d₀ A L a) x f = d (a • f.curryLeft x) - a • d (f.curryLeft x)

@[simp]
def d_aux_zero : DifferentialAuxSystem A L M 0 := {
  d := {
    toFun f := {
      toFun v := ⁅v 0, f ![]⁆
      map_update_add' := by simp
      map_update_smul' := by simp [smul_lier]
      map_eq_zero_of_eq' := by simp
    }
    map_add' := by intros; ext; simp
    map_zero' := by ext; simp
  }
  d' := 0
  curryLeft_d := by simp; intros; ext; simp
  contr_eq := by
    intros
    ext
    simp [contr_apply, lier_smul]
    congr
    ext i
    cases i using Fin.cases
    case zero => simp
    case succ i =>
      cases i
      contradiction
}

@[simp]
def d_aux_succ (n : ℕ) (sys : DifferentialAuxSystem A L M n) : DifferentialAuxSystem A L M (n + 1) := {
  d := {
    toFun f := uncurryLeft {
      toFun x := ⁅x, f⁆ - sys.d (f.curryLeft x)
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub, smul_lier, sys.contr_eq]; abel
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
  contr_eq := by
    intros a x f
    ext v
    simp [contr_apply_succ, Matrix.vecCons, smul_sub, sys.contr_eq, lier_smul]
    conv_lhs =>
        arg 1
        rw [curryLeft_skew]
    have : Fin.cons x (Fin.tail v) = Function.update v 0 x := by
      ext i
      cases i using Fin.cases
      case zero => simp
      case succ i => simp; rfl
    rw [this]
    simp
    abel
}

@[simp]
def d_aux (n : ℕ) : DifferentialAuxSystem A L M n := by
  induction n with
  | zero => exact d_aux_zero A L M
  | succ n ih => exact d_aux_succ A L M n ih

def d (n : ℕ) : (L [⋀^Fin n]→ₗ[A] M) →+ (L [⋀^Fin (n+1)]→ₗ[A] M) := (d_aux A L M n).d

end

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LRModule A L M] [LRModule.IsTrivial A L M]

@[simp]
theorem curryLeft_d_of_zero (f : L [⋀^Fin 0]→ₗ[A] M) (x : L) : (d A L M 0 f).curryLeft x = ⁅x, f⁆ := (d_aux A L M 0).curryLeft_d x f

@[simp]
theorem d_apply_zero (f : L [⋀^Fin 0]→ₗ[A] M) (v : Fin 1 → L) : d A L M 0 f v = ⁅v 0, f ![]⁆ := by
  simp [d]

@[simp]
theorem curryLeft_d_of_succ (n : ℕ) (f : L [⋀^Fin (n+1)]→ₗ[A] M) (x : L) : (d A L M (n+1) f).curryLeft x = ⁅x, f⁆ - d A L M (n) (f.curryLeft x) := (d_aux A L M (n+1)).curryLeft_d x f

@[simp]
theorem d_apply_succ (f : L [⋀^Fin (n+1)]→ₗ[A] M) (v : Fin (n + 2) → L) : d A L M (n+1) f v = ⁅v 0, f⁆ (Fin.tail v) - d A L M (n) (f.curryLeft (v 0)) (Fin.tail v) := by
  simp [d]

theorem d_lie (n : ℕ) (x : L) (f : L [⋀^Fin n]→ₗ[A] M) :
  d A L M n (⁅x, f⁆) = ⁅x, d A L M n f⁆ := by
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
theorem d_d_apply (n : ℕ) (f : L [⋀^Fin n]→ₗ[A] M) : d A L M _ (d A L M _ f) = 0 := by
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

end Cochain
