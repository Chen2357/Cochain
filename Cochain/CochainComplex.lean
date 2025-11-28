import Cochain.Differential
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Abelian

namespace Cochain

def complex (A L M : Type*)
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] [LieRinehartModule A L M] [LieRinehartModule.IsTrivial A L M] :
  CochainComplex (AddCommGrpCat) ℕ where
  X n := AddCommGrpCat.of (L [⋀^Fin n]→ₗ[A] M)
  d n m := AddCommGrpCat.ofHom (if h : n + 1 = m then
    h ▸ AlternatingMap.d n
  else 0)
