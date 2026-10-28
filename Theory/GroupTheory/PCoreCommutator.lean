module
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutators with the core of an overgroup

If a normal subgroup C is contained in H, then its commutator with O_p(H)
lies in O_p(C), hence in O_p(G). Both normalizations put the commutator in
C ∩ O_p(H), and restriction of the core gives the conclusion.

This is the core commutator calculation used in Aschbacher--Smith 14.1.17(3).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem commutator_pCoreIn_le_of_normal {p : ℕ} (C H : Subgroup G)
    [C.Normal] (hCH : C ≤ H) : ⁅C,H.pCoreIn p⁆ ≤ pCore p G := by
  have hHN : H ≤ normalizer (H.pCoreIn p : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore p H).le_normalizer_map H.subtype
  have hcore : C.pCoreIn p ≤ pCore p G := by
    unfold pCoreIn
    rw [pCore_eq_comap_of_normal]
    exact map_comap_le _ _
  apply le_trans _ ((inf_pCoreIn_le_of_le p hCH).trans hcore)
  refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp (hCH.trans hHN))
  exact commutator_le_left _ _

end Subgroup
