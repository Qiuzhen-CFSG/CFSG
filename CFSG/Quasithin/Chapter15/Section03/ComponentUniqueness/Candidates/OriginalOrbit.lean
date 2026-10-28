module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SourceSQTK

/-!
# The literal cubic residual in an outside component orbit

The original known-simple 1.2.1 theorem supplies the nonnormal model and
index. The cubic residual theorem then maps through the actual inclusion
into G, and the index-two orbit identifies the full orbit with the Sylow span.

Source: Aschbacher--Smith 1.2.1--2 and 15.3.37, printed pp.504--505,1135.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

/-- Transport the source residual through the literal outside subgroup and
identify its span with the original Sylow span. -/
theorem source_threeResidual_eq_nonnormal_orbit
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    [IsQuasisimple ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I))]
    [IsSimpleGroup ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I))]
    (hd : 3 ∣ Nat.card ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hlt : L < localSpan L d.S) :
    (primeToResidual 3 I).map I.subtype = localSpan L d.S := by
  have hQ := OutsideStructure.outside_twoCoreQuotient_sqtk hG d hI
  have hSI : d.S ≤ I := le_sup_right.trans hI.1.2
  have hn : ¬ (L.subgroupOf I).Normal := by
    intro hN
    exact hlt.not_ge (conjugateSpanBy_le le_rfl
      (hSI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hN)))
  obtain ⟨hi, hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ hL).resolve_left hn
  have he := nonnormal_component_threeResidual hL hi hd
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 Nat.prime_three (by decide)) hm
  have hidx : (normalizer (L : Set G)).relIndex I ≤ 2 := by
    change ((normalizer (L : Set G)).subgroupOf I).index ≤ 2
    rw [subgroupOf_normalizer_eq hLI]
    exact hi.le
  rw [he, map_conjugateSpanBy, map_subgroupOf_eq_of_le hLI,
    ← MonoidHom.range_eq_map, range_subtype]
  exact localSpan_eq_of_nontrivial_orbit hSI hlt hidx

end CFSG.Quasithin.Chapter15.Section03.Candidates
