module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.TINormalizerControl

/-!
# Original 12.2 normalizers and trivial intersections

The genuine structural theorem 12.2.2 supplies T-invariance and TI for the
original chosen module. Source 1.2.7, derived from Theorems A and C, makes
N(L) the unique maximal two-local over LT. This places the full N(V) in
N(L), and proves 12.2.6 for every nontrivial subgroup of the actual V.
The structural theorem is an explicit earlier dependency; no higher-rank
flag, module span or desired normalizer conclusion is assumed.

Source: Aschbacher--Smith, 12.2.2 and 12.2.6, printed pp.794--797.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Hypothesis1221
variable (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
variable (hT : (T : Subgroup G) ≤ normalizer (L : Set G))
variable (hA : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
variable (hC : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
include hT

omit [Finite G] in
theorem sylow_normalized_orbit_eq : componentOrbit L (T : Subgroup G) = L := by
  apply le_antisymm _ (le_componentOrbit L _)
  exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hT

include h hA hC

theorem sylow_normalized_maximal_unique :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC
    h.simpleQTKE T h.maximal_faithful.1
  simpa only [sylow_normalized_orbit_eq hT] using
    And.intro hu.normalizer_maximal hu.normalizer_unique

theorem sylow_normalized_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)) :=
  h.simpleQTKE.twoLocal_sqtk (h.sylow_normalized_maximal_unique hT hA hC).1.1

theorem sylow_normalized_component :
    (L.subgroupOf (normalizer (L : Set G))).IsCComponent := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC hA hC
    h.simpleQTKE T h.maximal_faithful.1
  exact hu.component _ ⟨Chapter1.mem_H_of_isTwoLocal
    (h.sylow_normalized_maximal_unique hT hA hC).1.1, sup_le L.le_normalizer hT⟩
end Hypothesis1221

namespace Hypothesis1223
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
variable (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
variable (hA : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
variable (hC : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
include h structural

theorem source_sylow_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G) :=
  (structural G T L h).1

theorem source_chosen_TI (D : ChosenModule T L V) :
    ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V :=
  ((structural G T L h).2.2 V D).2.2.1

theorem source_orbit_eq : componentOrbit L (T : Subgroup G) = L :=
  Hypothesis1221.sylow_normalized_orbit_eq (h.source_sylow_normalizes structural)

include hA hC

theorem source_normalizer_maximal_unique :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) :=
  h.toHypothesis1221.sylow_normalized_maximal_unique
    (h.source_sylow_normalizes structural) hA hC

theorem source_normalizer_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)) :=
  h.toHypothesis1221.sylow_normalized_sqtk (h.source_sylow_normalizes structural) hA hC

theorem source_normalizer_component :
    (L.subgroupOf (normalizer (L : Set G))).IsCComponent :=
  h.toHypothesis1221.sylow_normalized_component (h.source_sylow_normalizes structural) hA hC

theorem source_chosen_normalizer_le (D : ChosenModule T L V) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  exact normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural hA hC).2
    (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)

theorem source_intersection_normalizer (D : ChosenModule T L V)
    {U H : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hH : H ≤ normalizer (U : Set G)) :
    H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G) :=
  inf_eq_inf_normalizer_of_trivial_intersections (h.source_chosen_TI structural D)
    (h.source_chosen_normalizer_le structural hA hC D) hU hUV hH

omit hA hC in
theorem source_point_normalizes_chosen (D : ChosenModule T L V)
    {v : G} (hv : v ∈ V) (hne : v ≠ 1) {Y : Subgroup G}
    (hY : Y ≤ normalizer (L : Set G) ⊓ centralizer ({v} : Set G)) :
    Y ≤ normalizer (V : Set G) :=
  hY.trans (inf_elementCentralizer_le_normalizer_of_trivial_intersections
    (h.source_chosen_TI structural D) hv hne)
end Hypothesis1223
end CFSG.Quasithin.Chapter12.Section02
