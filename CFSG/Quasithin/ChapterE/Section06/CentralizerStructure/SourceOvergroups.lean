module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import Theory.Quasithin.Rank
/-!
# SQTK and full component orbits in the original E.6 local overgroups

An actual subgroup with nontrivial two-core embeds in the two-local normalizer
of that core. Hypothesis E.6.1 gives SQTK for this subgroup and its actual
quotient by the two-core. The complete 1.2.1(3) source then supplies both relative
normality/orbit size and the four-model list on the original component quotient.
No abstract quotient actor or extra ordinary-component hypothesis is introduced.
Source: Aschbacher–Smith, 1.2.1(3), E.6.8 and E.6.23, pp.504,247,254–255.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

theorem source_local_sqtk (h : HypothesisE61 K T M V)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK K H := by
  let R := H.pCoreIn 2
  have hHN : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((h.simpleQTKE.twoLocal_sqtk ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩).subgroup
      (H.subgroupOf (normalizer (R : Set G))))

theorem source_local_twoCore_quotient_sqtk (h : HypothesisE61 K T M V)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK K (H ⧸ pCore 2 H) := by
  have hs := source_local_sqtk h hH
  refine ⟨?_,hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

theorem source_cComponent_orbits_and_models
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) {B : Subgroup H} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B) :=
  Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (source_local_twoCore_quotient_sqtk h hH) hB

end CFSG.Quasithin.ChapterE.Section06
