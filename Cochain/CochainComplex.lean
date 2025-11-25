import Cochain.Differential
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Abelian

namespace Cochain

def complex (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] [LRModule A L M] [LRModule.IsTrivial A L M] :
  CochainComplex (AddCommGrpCat) ℕ where
  X n := AddCommGrpCat.of (L [⋀^Fin n]→ₗ[A] M)
  d n m := AddCommGrpCat.ofHom (if h : n + 1 = m then
    h ▸ AlternatingMap.d A L M n
  else 0)
