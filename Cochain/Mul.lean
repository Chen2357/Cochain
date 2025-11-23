import Cochain.Basic

namespace Cochain

namespace Aux

open AlternatingMap

variable (A L M : Type*)
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [CommRing M] [Algebra A M]

structure MulSystem₁ (m : ℕ) where
  mul : ∀ k l, (L [⋀^Fin k]→ₗ[A] M) →ₗ[M] (L [⋀^Fin m]→ₗ[A] M) →ₗ[M] (L [⋀^Fin l]→ₗ[A] M)
  mul' : ∀ k l, (L [⋀^Fin k]→ₗ[A] M) →ₗ[M] (L [⋀^Fin (m-1)]→ₗ[A] M) →ₗ[M] (L [⋀^Fin l]→ₗ[A] M)
  curryLeft_mul₀ : ∀ f : L [⋀^Fin 0]→ₗ[A] M, ∀ g : L [⋀^Fin m]→ₗ[A] M, mul 0 m f g = (f ![]) • g
  curryLeft_mul₁ : ∀ k : ℕ, ∀ f : L [⋀^Fin (k + 1)]→ₗ[A] M, ∀ g : L [⋀^Fin m]→ₗ[A] M, match m, mul, mul', g with
    | 0, mul, _, g => mul (k+1) (k+1) f g = (g ![]) • f
    | m + 1, mul, mul', g => ∀ x : L, (mul (k + 1) (k + m + 2) f g).curryLeft x = mul (k) (k + m + 1) (f.curryLeft x) g + (-1)^(k + 1) • mul' (k+1) (k + m + 1) f (g.curryLeft x)
  g : ∀ k l, (k + m ≠ l) → mul k l = 0
  g' : ∀ k l, (k + m - 1 ≠ l) → mul' k l = 0

structure MulSystem₂ (n m : ℕ) (sys : MulSystem₁ A L M (m-1)) where
  mul : ∀ l, (L [⋀^Fin n]→ₗ[A] M) →ₗ[M] (L [⋀^Fin m]→ₗ[A] M) →ₗ[M] (L [⋀^Fin l]→ₗ[A] M)
  mul' : ∀ l, (L [⋀^Fin (n-1)]→ₗ[A] M) →ₗ[M] (L [⋀^Fin m]→ₗ[A] M) →ₗ[M] (L [⋀^Fin l]→ₗ[A] M)
  curryLeft_mul : ∀ f : L [⋀^Fin n]→ₗ[A] M, ∀ g : L [⋀^Fin m]→ₗ[A] M, match n, m with
    | 0, m => mul m f g = (f ![]) • g
    | n, 0 => mul n f g = (g ![]) • f
    | n + 1, m + 1 => ∀ x : L, (mul (n + m + 2) f g).curryLeft x = mul' (n + m + 1) (f.curryLeft x) g + (-1)^(n+1) • sys.mul (n+1) (n + m + 1) f (g.curryLeft x)
  g : ∀ l, (n + m ≠ l) → mul l = 0
  g' : ∀ l, (n + m - 1 ≠ l) → mul' l = 0

@[simp]
def mul_sys₁.zero: MulSystem₁ A L M 0 where
  mul k l := if h : k = l then
      {
        toFun f := {
          toFun g := h ▸ {
            toFun v := (f v) • (g ![])
            map_update_add' := by simp [add_mul]
            map_update_smul' := by simp
            map_eq_zero_of_eq' v i j h hij := by rw [map_eq_zero_of_eq f v h hij, zero_smul]
          }
          map_add' := by induction h; intros; ext; simp [mul_add]
          map_smul' := by induction h; intros; ext; simp; ring
        }
        map_add' := by induction h; intros; ext; simp [add_mul]
        map_smul' := by induction h; intros; ext; simp [mul_assoc]
      }
    else 0
  mul' k l := 0
  curryLeft_mul₀ f g := by simp; ext; simp; congr; all_goals apply Subsingleton.elim
  curryLeft_mul₁ := by intros; ext; simp; rw [mul_comm]
  g k l h := by split; contradiction; rfl
  g' k l h := rfl

@[simp]
def mul_sys₂.zero (m : ℕ) (sys : MulSystem₁ A L M (m-1)) : MulSystem₂ A L M 0 m sys where
  mul l := if h : m = l then {
      toFun f := {
        toFun g := h ▸ ((f ![]) • g)
        map_add' := by induction h; simp
        map_smul' := by induction h; intros; ext; simp; ring
      }
      map_add' := by induction h; intros; ext; simp [add_mul]
      map_smul' := by induction h; intros; ext; simp [mul_assoc]
    }
    else 0
  mul' l := 0
  curryLeft_mul f g := by simp
  g l h := by simp at h; split; contradiction; rfl
  g' l h' := rfl

def mul_sys₂.succ.mul (n m : ℕ) (sys₁ : MulSystem₁ A L M m) (sys₂ : MulSystem₂ A L M n (m+1) sys₁) (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (g : L [⋀^Fin (m + 1)]→ₗ[A] M) : L [⋀^Fin ((n + 1) + (m + 1))]→ₗ[A] M :=
  uncurryLeft {
    toFun x := sys₂.mul (n + 1 + m) (f.curryLeft x) g + (-1)^(n + 1) • sys₁.mul (n + 1) (n + 1 + m) f (g.curryLeft x)
    map_add' := by intros; simp; abel
    map_smul' := by intros; simp; rw [smul_comm, ←algebraMap_smul (R:=A) (A:=M)]
  } <| by
    cases m
    case zero =>
      intro x
      simp
      have h1 := sys₂.curryLeft_mul (f.curryLeft x) g
      have h2 := sys₁.curryLeft_mul₁ _ f (g.curryLeft x)
      cases n
      case zero =>
        simp at *
        rw [h1, h2]
        ext v
        have : v = ![] := by apply Subsingleton.elim
        simp [Matrix.vecCons, this]
        ring
      case succ n =>
        have h3 := sys₁.curryLeft_mul₁ _ (f.curryLeft x) (g.curryLeft x)
        simp at *
        rw [h1, h2, h3]
        simp
        ring_nf
        rw [neg_smul]
        rw [neg_add_eq_zero]
        rfl
    case succ m =>
      intro x
      show (((sys₂.mul (n + 1 + (m + 1))) (f.curryLeft x)) g +
            (-1) ^ (n + 1) • ((sys₁.mul (n + 1) (n + 1 + (m + 1))) f) (g.curryLeft x)).curryLeft x = 0
      have h1 := sys₂.curryLeft_mul (f.curryLeft x) g
      have h2 := sys₁.curryLeft_mul₁ _ f (g.curryLeft x) x
      cases n
      case zero =>
        simp at *
        have : m + 1 = 1 + m := add_comm _ _
        apply Eq.ndrec (motive := fun (t : ℕ) => (((sys₂.mul (t + 1)) (f.curryLeft x)) g).curryLeft x + (-((sys₁.mul 1 (t + 1)) f) (g.curryLeft x)).curryLeft x = 0) (h:=this)
        have h2 : (((sys₁.mul 1 (m + 1 + 1)) f) (g.curryLeft x)).curryLeft x = ((sys₁.mul 0 (m + 1)) (f.curryLeft x)) (g.curryLeft x) := by
          apply Eq.ndrec (motive := fun (t : ℕ) => (((sys₁.mul 1 (t + 2)) f) (g.curryLeft x)).curryLeft x = ((sys₁.mul 0 (t + 1)) (f.curryLeft x)) (g.curryLeft x)) h2
          exact zero_add m
        simp [←curryLeftLinearMap_apply]
        have h3 := sys₁.curryLeft_mul₀ (f.curryLeft x) (g.curryLeft x)
        ext v
        simp [h1, h2, h3]
      case succ n =>
        simp at *
        have : (n + (m + 1) + 1) = (n + 1 + 1 + m) := by abel
        apply Eq.ndrec (motive := fun (t : ℕ) => (((sys₂.mul (t + 1)) (f.curryLeft x)) g).curryLeft x + ((-1) ^ (n + 1 + 1) • ((sys₁.mul (n + 1 + 1) (t + 1)) f) (g.curryLeft x)).curryLeft x = 0) (h:=this)
        have h2 : (((sys₁.mul (n + 1 + 1) (n + (m + 1) + 2)) f) (g.curryLeft x)).curryLeft x = ((sys₁.mul (n + 1) (n + (m + 1) + 1)) (f.curryLeft x)) (g.curryLeft x) := by
          apply Eq.ndrec (motive := fun (t : ℕ) => (((sys₁.mul (n + 1 + 1) (t + 2)) f) (g.curryLeft x)).curryLeft x = ((sys₁.mul (n + 1) (t + 1)) (f.curryLeft x)) (g.curryLeft x)) h2
          abel
        simp [←curryLeftLinearMap_apply]
        simp
        rw [h1, h2]
        simp
        ring_nf
        rw [neg_smul]
        rw [neg_add_eq_zero]

@[simp]
theorem mul_sys₂.succ.mul_curryLeft (n m : ℕ) (sys₁ : MulSystem₁ A L M m) (sys₂ : MulSystem₂ A L M n (m+1) sys₁) (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (g : L [⋀^Fin (m + 1)]→ₗ[A] M) (x : L) :
  (mul_sys₂.succ.mul A L M n m sys₁ sys₂ f g).curryLeft x = sys₂.mul (n + 1 + m) (f.curryLeft x) g + (-1)^(n + 1) • sys₁.mul (n + 1) (n + 1 + m) f (g.curryLeft x) := rfl

@[simp]
def mul_sys₂.succ (n m : ℕ) (sys₁ : MulSystem₁ A L M m) (sys₂ : MulSystem₂ A L M n (m+1) sys₁) : MulSystem₂ A L M (n + 1) (m+1) sys₁ where
  mul l := if h : (n + 1) + (m + 1) = l then {
      toFun f := {
        toFun g := h ▸ mul_sys₂.succ.mul A L M n m sys₁ sys₂ f g
        map_add' := by
          intros g₁ g₂
          induction h
          apply eq_of_curryLeft
          intro x
          simp [-Nat.add_eq]
          abel
        map_smul' := by
          intros a g
          induction h
          apply eq_of_curryLeft
          intro x
          simp [-Nat.add_eq]
          rw [smul_comm]
      }
      map_add' := by
        intros f₁ f₂
        ext1 g
        induction h
        apply eq_of_curryLeft
        intro x
        simp [-Nat.add_eq]
        abel
      map_smul' := by
        intros a f
        ext1 g
        induction h
        apply eq_of_curryLeft
        intro x
        simp [-Nat.add_eq]
        rw [smul_comm]
    }
    else 0
  mul' l := sys₂.mul l
  curryLeft_mul f g := by
    intro x
    apply Eq.trans (b := (if h : n + 1 + (m + 1) = (n + m + 2) then (h ▸ succ.mul A L M n m sys₁ sys₂ f g).curryLeft x else 0))
    have : n + 1 + (m + 1) = n + m + 2 := by linarith
    simp [this]

    show (if h : n + 1 + (m + 1) = n + m + 1 + 1 then (h ▸ succ.mul A L M n m sys₁ sys₂ f g).curryLeft x else 0) = ((sys₂.mul (n + m + 1)) (f.curryLeft x)) g + (-1) ^ (n + 1) • ((sys₁.mul (n + 1) (n + m + 1)) f) (g.curryLeft x)
    have : n + 1 + m = n + m + 1 := by linarith
    let motive t := (
      (if h : n + 1 + (m + 1) = (t + 1) then (h ▸ succ.mul A L M n m sys₁ sys₂ f g).curryLeft x else 0) =
      sys₂.mul t (f.curryLeft x) g + (-1) ^ (n + 1) • (sys₁.mul (n + 1) t f (g.curryLeft x))
    )
    apply Eq.ndrec (motive := motive) (h:=this)
    have : n + 1 + (m + 1) = n + 1 + m + 1 := rfl
    simp [this, motive]
    apply mul_sys₂.succ.mul_curryLeft
  g l h := by
    split
    case isTrue h' =>
      exfalso
      apply h
      rw [←h']
    rfl
  g' l h := sys₂.g l <| by
    simp at h
    intro h'
    apply h
    rw [←h']
    linarith

@[simp]
def mul_sys₂ (n m : ℕ) (sys : MulSystem₁ A L M m) : MulSystem₂ A L M n (m+1) sys := match n with
  | 0 => mul_sys₂.zero A L M (m + 1) sys
  | n + 1 => mul_sys₂.succ A L M n m sys (mul_sys₂ n m sys)

@[simp]
def mul_sys₁.succ (m : ℕ) (sys : MulSystem₁ A L M m) : MulSystem₁ A L M (m + 1) where
  mul k l := (mul_sys₂ A L M k m sys).mul l
  mul' := sys.mul
  curryLeft_mul₀ := by simp
  curryLeft_mul₁ k := (mul_sys₂ A L M (k + 1) m sys).curryLeft_mul
  g k l h := (mul_sys₂ A L M k m sys).g l h
  g' k l h' := sys.g k l <| by
    simp at h'
    exact h'

@[simp]
def mul_sys₁ (m : ℕ) : MulSystem₁ A L M m := match m with
  | 0 => mul_sys₁.zero A L M
  | n + 1 => mul_sys₁.succ A L M n (mul_sys₁ n)

end Aux

open AlternatingMap

namespace AlternatingMap

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [CommRing M] [Algebra A M]

def mul (n m l) : (L [⋀^Fin n]→ₗ[A] M) →ₗ[M] (L [⋀^Fin m]→ₗ[A] M) →ₗ[M] (L [⋀^Fin l]→ₗ[A] M) := (Aux.mul_sys₁ A L M m).mul n l

theorem mul_of_ne (n m l) (h : n + m ≠ l) :
  mul (A:=A) (L:=L) (M:=M) n m l = 0 :=
  (Aux.mul_sys₁ A L M m).g n l h

@[simp]
theorem mul_deg_zero_apply (f : L [⋀^Fin 0]→ₗ[A] M) (g : L [⋀^Fin 0]→ₗ[A] M) (n : ℕ) (v : Fin n → L) :
  mul 0 0 n f g v = if n = 0 then f ![] * g ![] else 0 := by
  split
  case isTrue h =>
    cases h
    simp [mul]
    congr
    apply Subsingleton.elim
  case isFalse h =>
    rw [mul_of_ne]
    simp
    exact fun a => h (Eq.symm a)

theorem mul_deg_zero_eq_ite {n l} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin 0]→ₗ[A] M) :
  (mul _ _ l f g) = if h : n = l then h ▸ ((g ![]) • f) else 0 := by
  by_cases h : n = l
  simp [mul]
  induction h
  simp
  ext
  simp
  ring
  simp [h]
  rw [mul_of_ne]
  simp
  exact h

theorem deg_zero_mul_eq_ite {n l} (f : L [⋀^Fin 0]→ₗ[A] M) (g : L [⋀^Fin n]→ₗ[A] M) :
  (mul _ _ l f g) = if h : n = l then h ▸ ((f ![]) • g) else 0 := by
  by_cases h : n = l
  simp [mul]
  induction h
  simp
  ext
  simp
  induction n
  simp
  congr
  apply Subsingleton.elim
  apply Subsingleton.elim
  simp
  simp [h]
  rw [mul_of_ne]
  simp
  rw [zero_add]
  exact h

@[simp]
theorem mul_deg_succ_eq_zero {n m} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin (m + 1)]→ₗ[A] M) :
  mul _ _ 0 f g = 0 := by
  rw [mul_of_ne]
  simp
  simp

@[simp]
theorem deg_succ_mul_eq_zero {n m} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  mul _ _ 0 f g = 0 := by
  rw [mul_of_ne]
  simp
  simp

@[simp]
theorem mul_deg_zero_same {n} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin 0]→ₗ[A] M) :
  (mul _ _ n f g) = (g ![]) • f := by
  simp [mul]
  ext
  simp
  ring

@[simp]
theorem deg_zero_mul_same {n} (f : L [⋀^Fin 0]→ₗ[A] M) (g : L [⋀^Fin n]→ₗ[A] M) :
  (mul _ _ n f g) = (f ![]) • g := by
  simp [mul]
  ext
  simp
  induction n
  simp
  congr
  apply Subsingleton.elim
  apply Subsingleton.elim
  simp

@[simp]
theorem mul_deg_zero_curryLeft {n l} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (g : L [⋀^Fin 0]→ₗ[A] M) (x : L) :
  (mul _ _ (l + 1) f g).curryLeft x = mul _ _ l (f.curryLeft x) g := by
  by_cases h : l = n
  rw [h]
  simp
  ext v
  simp
  rw [mul_of_ne]
  rw [mul_of_ne]
  simp
  all_goals exact fun h' => h (by linarith)

@[simp]
theorem deg_zero_mul_curryLeft {n l} (f : L [⋀^Fin 0]→ₗ[A] M) (g : L [⋀^Fin (n + 1)]→ₗ[A] M) (x : L) :
  (mul _ _ (l + 1) f g).curryLeft x = mul _ _ l f (g.curryLeft x) := by
  by_cases h : l = n
  rw [h]
  simp
  ext v
  simp [Matrix.vecCons]
  rw [mul_of_ne]
  rw [mul_of_ne]
  simp
  all_goals exact fun h' => h (by linarith)

@[simp]
theorem mul_curryLeft {n m l} (f : L [⋀^Fin (n + 1)]→ₗ[A] M) (g : L [⋀^Fin (m + 1)]→ₗ[A] M) (x : L) :
  (mul _ _ (l + 1) f g).curryLeft x =
    mul _ _ l (f.curryLeft x) g +
    (-1)^(n + 1) • mul _ _ l f (g.curryLeft x) := by
  by_cases h : l = n + m + 1
  unfold mul
  have := (Aux.mul_sys₁ A L M (m + 1)).curryLeft_mul₁ n f g
  simp [-Aux.mul_sys₁] at this
  rw [h]
  apply this
  rw [mul_of_ne]
  rw [mul_of_ne]
  rw [mul_of_ne]
  simp
  intro h'
  apply h
  rw [←h']
  abel
  exact fun h' => h (h'.symm)
  intro h'
  apply h
  apply Nat.add_one_inj.mp
  rw [←h']
  abel

theorem mul_graded_comm {n m l} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) :
  mul _ _ l f g = (-1)^(m * n) • mul _ _ l g f := by
  revert l
  induction n, m using Nat.pincerRecursion
  case Ha0 => simp [deg_zero_mul_eq_ite, mul_deg_zero_eq_ite]
  case H0b => simp [deg_zero_mul_eq_ite, mul_deg_zero_eq_ite]
  case H n m hn hm =>
    intro l
    cases l
    case zero => simp
    case succ l =>
      apply eq_of_curryLeft
      intro x
      simp [←curryLeftLinearMap_apply]
      simp
      rw [@hn (f.curryLeft x) g l, @hm f (g.curryLeft x) l, add_comm]
      simp [smul_smul, ←Int.pow_add]
      congr 2
      apply neg_one_pow_congr
      apply Nat.even_add.mp
      use (1 + n + m + n * m)
      ring
      apply neg_one_pow_congr
      apply Nat.even_add.mp
      use (1 + n + m + n * m)
      ring

theorem mul_assoc {n m l i} (f : L [⋀^Fin n]→ₗ[A] M) (g : L [⋀^Fin m]→ₗ[A] M) (h : L [⋀^Fin l]→ₗ[A] M) :
  mul _ _ i (mul _ _ (n + m) f g) h = mul _ _ i f (mul _ _ (m + l) g h) := match n, m, l with
  | 0, 0, 0 => by
    by_cases hi : i = 0
    rw [hi]
    ext v
    simp
    ring
    rw [mul_of_ne]
    simp
    exact fun h' => hi (by linarith)
  | 0, 0, l + 1 => by
    by_cases hi : i = l + 1
    rw [hi]
    ext v
    simp
    have : 0 + (l + 1) = l + 1 := by linarith
    rw [this]
    simp
    ring
    rw [mul_of_ne]
    nth_rw 2 [mul_of_ne]
    simp
    all_goals exact fun h' => hi (by linarith)
  | 0, m + 1, 0 => by
    have : 0 + (m + 1) = m + 1 := by linarith
    rw [this]
    by_cases hi : i = m + 1
    rw [hi]
    simp [smul_smul]
    ring_nf
    rw [mul_of_ne]
    nth_rw 2 [mul_of_ne]
    simp
    all_goals exact fun h' => hi (by linarith)
  | 0, m + 1, l + 1 => by
    have : 0 + (m + 1) = m + 1 := by linarith
    rw [this]
    by_cases hi : i = m + l + 2
    rw [hi]
    apply eq_of_curryLeft
    intro x
    have : m + 1 + (l + 1) = m + l + 2 := by linarith
    rw [this]
    simp
    rw [mul_of_ne]
    nth_rw 2 [mul_of_ne]
    simp
    all_goals exact fun h' => hi (by linarith)
  | n + 1, 0, 0 => by
    have : n + 1 = n + 1 + 0 := by linarith
    apply Eq.ndrec (motive := fun t => ((mul t 0 i) (((mul (n + 1) 0 t) f) g)) h = ((mul (n + 1) (0 + 0) i) f) (((mul 0 0 (0 + 0)) g) h)) (h := this)
    by_cases hi : i = n + 1
    rw [hi]
    ext v
    simp
    rw [mul_of_ne]
    simp
    exact fun h' => hi (by linarith)
  | n + 1, 0, l + 1 => by
    have : n + 1 = n + 1 + 0 := by linarith
    apply Eq.ndrec (motive := fun t => ((mul t (l + 1) i) (((mul (n + 1) 0 t) f) g)) h = ((mul (n + 1) (0 + (l + 1)) i) f) (((mul 0 (l + 1) (0 + (l + 1))) g) h)) (h := this)
    by_cases hi : i = n + l + 2
    rw [hi]
    apply eq_of_curryLeft
    intro x
    have : 0 + (l + 1) = l + 1 := by linarith
    rw [this]
    simp
    rw [mul_of_ne]
    nth_rw 2 [mul_of_ne]
    simp
    all_goals exact fun h' => hi (by linarith)
  | n + 1, m + 1, 0 => by
    have : n + 1 + (m + 1) = n + m + 2 := by linarith
    rw [this]
    by_cases hi : i = n + m + 2
    rw [hi]
    apply eq_of_curryLeft
    intro x
    simp
    rw [mul_of_ne]
    nth_rw 2 [mul_of_ne]
    simp
    all_goals exact fun h' => hi (by linarith)
  | n + 1, m + 1, l + 1 => by
    have h1 : n + 1 + (m + 1) = n + m + 2 := by linarith
    rw [h1]
    have : m + 1 + (l + 1) = m + l + 2 := by linarith
    rw [this]
    cases i
    case zero => simp
    case succ i =>
      apply eq_of_curryLeft
      intro x
      simp only [mul_curryLeft, Int.reduceNeg, map_add, LinearMap.map_smul_of_tower, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
      have : ((mul (n + m + 1) (l + 1) i) (((mul n (m + 1) (n + m + 1)) (f.curryLeft x)) g)) h = ((mul n (m + l + 2)) i) (f.curryLeft x) (((mul (m + 1) (l + 1) (m + l + 2)) g) h) := (by linarith : (m + 1 + (l + 1)) = (m + l + 2)) ▸ (mul_assoc (i:=i) (f.curryLeft x) g h)
      rw [this]
      have := (by linarith : (n + 1 + m) = (n + m + 1)) ▸ (mul_assoc (i:=i) f (g.curryLeft x) h)
      rw [this]
      have := (by linarith : (n + 1 + (m + 1)) = (n + m + 2)) ▸ (mul_assoc (i:=i) f g (h.curryLeft x))
      rw [this]
      rw [add_assoc, smul_smul, ←Int.pow_add, h1]
      congr 3
      have : m + 1 + l = m + l + 1 := by linarith
      rw [this]

end AlternatingMap

end Cochain
