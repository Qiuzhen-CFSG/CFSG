module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.OddCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.Rank

/-!
# SQTK inheritance for the original outside subgroup

An outside member has nontrivial two-core, hence lies in a proper maximal
two-local subgroup. The original proper-K hypothesis applies to this actual
member, and quasithinness gives its odd-rank bounds. A two-core quotient
preserves the K-group condition and cannot increase any odd prime rank.
This supplies the literal 1.2.1 input in Aschbacher--Smith15.3.12, pp.1124--1125.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

theorem outside_sqtk (hG : IsSimpleQTKE κ G)
    (d : CharacteristicTwo.LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus) :
    IsSQTK κ I := by
  have hc : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hc
  let := hG.simple
  have hp : I ≠ ⊤ := by
    intro he
    exact twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hN.1
      (top_unique (he ▸ hIN))
  exact ⟨outside_stronglyQuasithin hG.quasithin d.Yplus d.S d.M I hI,hG.properK I hp⟩

theorem outside_twoCoreQuotient_sqtk (hG : IsSimpleQTKE κ G)
    (d : CharacteristicTwo.LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus) :
    IsSQTK κ (I ⧸ pCore 2 I) := by
  have hQ := outside_sqtk hG d hI
  refine ⟨?_,hQ.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hQ.stronglyQuasithin p hp ho)

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
