module

public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# NormalizerSource at the original ambient group and Sylow subgroup

These are the same source arguments as `NormalizerSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.2.6, printed p.796; applied in 12.3.3–13.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Hypothesis1223

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

variable (hA : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)

variable (hC : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)

include h structural

set_option linter.unusedSectionVars false in
theorem source_sylow_normalizes_at : (T : Subgroup G) ≤ normalizer (L : Set G) :=
  (structural L h).1

set_option linter.unusedSectionVars false in
theorem source_chosen_TI_at (D : ChosenModule T L V) :
    ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V :=
  ((structural L h).2.2 V D).2.2.1

theorem source_orbit_eq_at : componentOrbit L (T : Subgroup G) = L :=
  Hypothesis1221.sylow_normalized_orbit_eq (h.source_sylow_normalizes_at structural)

include hA hC

theorem source_normalizer_maximal_unique_at :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) :=
  h.toHypothesis1221.sylow_normalized_maximal_unique
    (h.source_sylow_normalizes_at structural) hA hC

theorem source_normalizer_sqtk_at :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)) :=
  h.toHypothesis1221.sylow_normalized_sqtk (h.source_sylow_normalizes_at structural) hA hC

theorem source_normalizer_component_at :
    (L.subgroupOf (normalizer (L : Set G))).IsCComponent :=
  h.toHypothesis1221.sylow_normalized_component (h.source_sylow_normalizes_at structural) hA hC

theorem source_chosen_normalizer_le_at (D : ChosenModule T L V) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  exact normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural hA hC).2
    (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
    (sup_le D.normalizes ((structural L h).2.2 V D).1)

theorem source_intersection_normalizer_at (D : ChosenModule T L V)
    {U H : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hH : H ≤ normalizer (U : Set G)) :
    H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G) :=
  inf_eq_inf_normalizer_of_trivial_intersections (h.source_chosen_TI_at structural D)
    (h.source_chosen_normalizer_le_at structural hA hC D) hU hUV hH

omit hA hC in

theorem source_point_normalizes_chosen_at (D : ChosenModule T L V)
    {v : G} (hv : v ∈ V) (hne : v ≠ 1) {Y : Subgroup G}
    (hY : Y ≤ normalizer (L : Set G) ⊓ centralizer ({v} : Set G)) :
    Y ≤ normalizer (V : Set G) :=
  hY.trans (inf_elementCentralizer_le_normalizer_of_trivial_intersections
    (h.source_chosen_TI_at structural D) hv hne)

end Hypothesis1223

end CFSG.Quasithin.Chapter12.Section02

