module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Characteristic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.NonabelianRadical

/-!
# The characteristic subgroup in original 15.1.29

If the actual parabolic radical has no nontrivial characteristic subgroup
normal in KQ₂, the constructed rank-two data give a small MS pair. For an
abelian commutator core, the proved source alternatives contradict the
nonblock and centralizer markings. For a nonabelian core, the proved radical
inequality directly contradicts the same centralizer marking. This supplies
the required characteristic subgroup without a universal MS classification.

Source: Aschbacher--Smith, C.1.31--34, pp.135--137, and 15.1.29, p.1104.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData.NaturalRankTwoInput
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {p : NaturalParabolics d}

/-- The actual characteristic subgroup of Q₂, with normality relative to
KQ₂. Only the proved abelian alternatives and nonabelian radical inequality
are needed; no fixed-factor centrality assertion is used. -/
theorem exists_characteristic_normal_without_ms (b : NaturalRankTwoInput p) :
    ∃ C : Subgroup p.Q2, C.Characteristic ∧ C ≠ ⊥ ∧
      ((C.map p.Q2.subtype).subgroupOf (p.K ⊔ p.Q2)).Normal := by
  classical
  by_contra hnone
  have hchar : MSNoCharacteristicNormal p.K p.Q2 := by
    intro C hC hn
    by_contra hne
    exact hnone ⟨C,hC,hne,hn⟩
  have hms : SmallMSPair KnownSimple.IsKnownSimple p.K p.Q2 := {
    finite := inferInstance
    sqtk := b.sqtk
    fitting := b.fitting
    product := b.product
    component := b.component
    rankTwo := b.rankTwo
    radical := b.radical
    characteristic := hchar }
  obtain ⟨e⟩ := b.model
  by_cases hc : IsMulCommutative (msQ p.K p.Q2)
  · obtain ⟨e',he⟩ := hms.abelian_source e hc d.S b.sylow b.core_le_sylow
    rcases he with h1 | h2 | h3 | h4 | h5
    · exact b.not_linear_block h1.2.1
    · exact h2.2 b.centralizer_core
    · exact h3.2.2 b.centralizer_core
    · exact h4.2.2.2.2.2.2.2.2.2 b.centralizer_core
    · exact b.omega_not_central h5.2.2.2.1
  · exact hms.nonabelian_not_centralizer_core e hc b.sylow b.core_le_sylow
      b.centralizer_core

end CaseIComponentData.NaturalRankTwoInput
end CFSG.Quasithin.Chapter15.Section01
