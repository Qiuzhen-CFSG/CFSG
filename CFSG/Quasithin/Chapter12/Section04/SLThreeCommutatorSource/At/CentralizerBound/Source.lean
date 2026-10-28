module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo.Exclusion
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore.Layer.Source
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# Original L₃ hyperplane centralizers at the actual G,T

An escaping hyperplane has a characteristic-two centralizer, an ordinary
component, or a nontrivial odd core. The localized E.6.14 argument excludes
the first case; the literal plane-layer residual excludes the second; the
abelian odd closure and inversion by the fixed involution exclude the last.
All three cases use only the original same-G,T structural implication.

Source: Aschbacher–Smith, 12.4.8, printed pp.815–816.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
open Section02 SmallFusion ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Every actual hyperplane has centralizer contained in the module normalizer.
The normalizer action and all three local case exclusions are discharged. -/
theorem hyperplane_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  intro U hUV hcor
  by_contra hescape
  let c : Configuration T L V U :=
    ⟨h, D, E, hne, structural, normalizer_action h structural E hne,
      hUV, hcor, hescape⟩
  by_cases hc : HasCharacteristicTwo (centralizer (U : Set G))
  · exact CharacteristicTwo.characteristicTwoExclusion G T L V U c hc
  by_cases hcomp : ∃ K : Subgroup G, IsComponentIn K (centralizer (U : Set G))
  · exact ordinaryComponentExclusion G T L V U c hcomp
  have hnc : ∀ K : Subgroup G, ¬ IsComponentIn K (centralizer (U : Set G)) :=
    fun K hK => hcomp ⟨K, hK⟩
  apply OddCore.oddCoreExclusion G T L V U c hnc
  intro ho
  apply hc
  let H := centralizer (U : Set G)
  have hnc' : ∀ J : Subgroup H, ¬ IsComponent H J := by
    intro J hJ
    apply hnc (J.map H.subtype)
    refine ⟨map_subtype_le J, ?_⟩
    have he : (J.map H.subtype).subgroupOf H = J :=
      comap_map_eq_self_of_injective H.subtype_injective J
    rwa [he]
  have hh := centralizer_core_product_le_of_no_components 2 hnc'
  change pPrimeCore 2 H = ⊥ at ho
  simpa only [HasCharacteristicTwo, ho, sup_bot_eq] using hh

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
