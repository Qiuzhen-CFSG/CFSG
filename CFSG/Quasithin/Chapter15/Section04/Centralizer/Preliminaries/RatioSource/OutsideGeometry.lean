module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.CommonNormal

/-!
# Applying the minimal-parabolic hypotheses in the outside-core case

The original embedded V lies in T. Its containment in O₂(M) therefore
restricts to O₂(H ∩ M). The normalizer of V inside H is a proper overgroup
of T whenever V is outside O₂(H), so minimality of H places that normalizer
inside H ∩ M. These verify the subgroup hypotheses used by E.2.8–9 without
requiring H to normalize V.

Source: Aschbacher–Smith, 15.4.2(4), case (i), printed p.1156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {M₀ M H : Subgroup G} {V : Subgroup M₀}

/-- The original reduced module lies in the actual ambient Sylow subgroup. -/
theorem LocalHypotheses.module_le_sylow (l : LocalHypotheses T M₀ M V) :
    V.map M₀.subtype ≤ (T : Subgroup G) :=
  (map_mono l.reduced.le_pCore).trans (l.core_eq_centralizer.le.trans inf_le_left)

/-- Containment in O₂(M) restricts to the actual intersection H ∩ M. -/
theorem LocalHypotheses.module_le_intersection_core (l : LocalHypotheses T M₀ M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    V.map M₀.subtype ≤ (H ⊓ M).pCoreIn 2 := by
  have hVH : V.map M₀.subtype ≤ H := l.module_le_sylow.trans hH.1.1.2
  have hVM : V.map M₀.subtype ≤ M := (map_subtype_le V).trans l.le_maximal
  exact (le_inf (le_inf hVH hVM) l.le_core).trans (inf_pCoreIn_le_of_le 2 inf_le_right)

/-- In case (i), the relative normalizer lies in H ∩ M. -/
theorem LocalHypotheses.normalizer_le_intersection (l : LocalHypotheses T M₀ M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hout : ¬ V.map M₀.subtype ≤ H.pCoreIn 2) :
    H ⊓ normalizer (V.map M₀.subtype : Set G) ≤ H ⊓ M := by
  let := l.reduced.elementary
  let : IsElementaryAbelian 2 (V.map M₀.subtype) := IsElementaryAbelian.map M₀.subtype
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hproper : H ⊓ normalizer (V.map M₀.subtype : Set G) < H := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hn : H ≤ normalizer (V.map M₀.subtype : Set G) := he ▸ inf_le_right
    exact hout (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
      (l.module_le_sylow.trans hTH) hn)
  exact le_inf inf_le_left (Chapter3.HStar.proper_overgroup_le T hH
    (le_inf hTH (l.mem_H.2.trans l.normalizes)) hproper)

end CFSG.Quasithin.Chapter15.Section04.RatioSource
