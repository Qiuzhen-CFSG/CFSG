module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RemainingModels
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.OrdinaryModels

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RemainingModels`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open ChapterA.Section02 ClassificationModels
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original covering relation supplies the literal quotient and
relative normality; the remaining central quotients are actual sporadic models. -/
theorem unitary_original_pushingUp_remaining_component (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    IsComponent H K ∧ ∃ n : SporadicName,
      (n = .j4 ∨ n = .ru) ∧
      Nonempty (K ⧸ center K ≃* n.Carrier) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique_at s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,e,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  let a := e.trans s.quotient
  have ho := hc.unitary_escaping_component_isComponent hn a K hK hq hout
  exact ⟨ho,hc.unitary_ordinary_two_sporadic_models a K ho⟩

/-- Failure of uniqueness selects the original pair and full module, with
every escaping component reduced to one of two actual sporadic quotients. -/
theorem unitary_original_oddActorResidual_remaining_pair (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      (∀ (K : Subgroup H), K.IsCComponent → IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H →
        IsComponent H K ∧ ∃ n : SporadicName,
          (n = .j4 ∨ n = .ru) ∧
          Nonempty (K ⧸ center K ≃* n.Carrier)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,⟨e,_⟩,_,_,hmark⟩ :=
    unitary_original_oddActorResidual_pushingUp s A hAN hcomm hodd hAV hnot
  exact ⟨J,H,S,hpush,hH,hJH,hlt,hc,fun K hK hq hout =>
    let ho := hc.unitary_escaping_component_isComponent hn e K hK hq hout
    ⟨ho,hc.unitary_ordinary_two_sporadic_models e K ho⟩,hmark⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
