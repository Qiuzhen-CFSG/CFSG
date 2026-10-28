module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Type
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Conjugation covariance of the original point cores

Conjugation transports the full point centralizer and its embedded two-core.
Intersecting with any preserved ambient subgroup commutes with that same
transport. These literal equalities support the point-incidence counts
without changing the original subgroups or their embeddings.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G]

/-- Conjugation transports the literal ambient two-core of a point
centralizer to the point core at the conjugate point. -/
theorem pointCore_conjugate (x g : G) :
    ((involutionCentralizer x).pCoreIn 2).map (MulAut.conj g).toMonoidHom =
      (involutionCentralizer (g * x * g⁻¹)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  change ((centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom).pCoreIn 2 = _
  rw [map_centralizer_equiv, Set.image_singleton, MulAut.conj_apply]

/-- A preserved original subgroup has conjugate point-core intersections
under that same ambient conjugation. -/
theorem pointCore_intersection_conjugate (A : Subgroup G) (x g : G)
    (hg : g ∈ normalizer (A : Set G)) :
    (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G).map
        (MulAut.conj g).toMonoidHom =
      A ⊓ (involutionCentralizer (g * x * g⁻¹)).pCoreIn 2 := by
  have hm : A.map (MulAut.conj g).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hg
  rw [map_inf _ _ _ (MulAut.conj g).injective, pointCore_conjugate, hm]

end CFSG.Quasithin.HigmanSims
