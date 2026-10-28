module

public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.Commutator.CentralizingFactor

/-!
# The terminal elementary calculations in general pushing up

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 4.1.5, printed pp. 607–608. An outside maximal two-local
overgroup and the core bounds in 4.1.4(5–6) force a centralizing subgroup into
`Z(R)`. The residual covering equality in 4.1.4(3) removes the centralizing
two-core factor from the commutator.

The core and residual-cover hypotheses below are explicit, undischarged inputs
from 4.1.4. These are assembly helpers, not assertions that 4.1.5 is proved.
-/

public section

namespace CFSG.Quasithin.Chapter4

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

/-- An actual counterexample supplies a maximal two-local overgroup outside
`M`, not merely an arbitrary subgroup containing `I`. -/
theorem exists_maximal_outside_of_mu [Finite G] {M Mplus Mminus I : Subgroup G}
    (hI : I ∈ mu M Mplus Mminus) :
    ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ I ≤ H ∧ ¬ H ≤ M := by
  obtain ⟨H, ⟨hcore, hIH⟩, hout⟩ := hI.2
  have hne : pCore 2 H ≠ ⊥ := by
    intro he
    exact hcore (by simp only [pCoreIn, he, Subgroup.map_bot])
  obtain ⟨L, hL, hHL⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hne
  exact ⟨L, hL, hIH.trans hHL, fun h => hout (hHL.trans h)⟩

/-- A maximal two-local contains the centralizer of its own two-core. -/
theorem centralizer_core_le_of_maximal {H : Subgroup G} (hH : IsMaximalTwoLocal H) :
    centralizer (H.pCoreIn 2 : Set G) ≤ H := by
  have hlocal : IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) :=
    ⟨H.pCoreIn 2, Chapter1.mem_H_of_isTwoLocal hH.1, isPGroup_pCoreIn 2 H, rfl⟩
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  exact (centralizer_le_normalizer _).trans (hH.eq_of_le hlocal hHN).symm.le

/-- The core-containment argument of 4.1.5(1), once 4.1.4(5–6) has been
proved for the chosen maximal outside overgroup. -/
theorem le_center_of_local_core_bounds {M H R V : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hVM : V ≤ M)
    (hVC : V ≤ centralizer (R : Set G))
    (hHR : H.pCoreIn 2 ≤ R) (hHMR : (H ⊓ M).pCoreIn 2 ≤ R)
    (hHe : H ⊓ M ∈ Chapter1.He G) : V ≤ (center R).map R.subtype := by
  have hVH : V ≤ H :=
    (hVC.trans (centralizer_le hHR)).trans (centralizer_core_le_of_maximal hH)
  have hVQ : V ≤ (H ⊓ M).pCoreIn 2 :=
    (le_inf (le_inf hVH hVM) (hVC.trans (centralizer_le hHMR))).trans hHe
  have hVR : V ≤ R := hVQ.trans hHMR
  intro v hv
  refine mem_map.mpr ⟨⟨v, hVR hv⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro r
  exact Subtype.ext (mem_centralizer_iff.mp (hVC hv) r r.property)

/-- The calculation of 4.1.5(3), from the residual covering equality supplied
by 4.1.4(3). No replacement of the two-residual by the two-core occurs. -/
theorem commutator_eq_of_residual_cover {Mplus H Rplus V : Subgroup G}
    (hcover : (Mplus : Set G) =
      ((pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype : Set G) *
        (Mplus.pCoreIn 2 : Set G))
    (hcore : Mplus.pCoreIn 2 ≤ Rplus) (hVC : V ≤ centralizer (Rplus : Set G))
    (hV : V = ⁅V, Mplus⁆) :
    V = ⁅V, (pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype⁆ :=
  hV.trans (commutator_eq_of_product_centralizing_factor hcover
    (hVC.trans (centralizer_le hcore)))

end CFSG.Quasithin.Chapter4
