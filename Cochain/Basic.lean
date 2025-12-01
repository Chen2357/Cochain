import LieRinehart.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Algebra.Group.TransferInstance

open DirectSum
open AlternatingMap
open Function

abbrev Cochain (A L M : Type*) [CommRing A] [LieRing L] [LieRinehartPair A L] [AddCommGroup M] [Module A M]  := DirectSum ℕ (fun n => L [⋀^Fin n]→ₗ[A] M)

namespace Cochain

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [CommRing M] [Algebra A M]

instance : IsScalarTower A M (L [⋀^Fin n]→ₗ[A] M) where
  smul_assoc := by
    intros r s f
    ext v
    simp [←algebraMap_smul (R:=A) (A:=M)]
    ring

@[simp]
theorem curryLeft_smul {n : ℕ} (m : M) (f : L [⋀^Fin n.succ]→ₗ[A] M) (x : L) : (m • f).curryLeft x = m • (f.curryLeft x) := rfl

end Cochain
