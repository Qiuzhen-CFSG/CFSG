module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.Reduction
public import CFSG.Quasithin.Chapter4.Section02.Unitary.IntersectionQuotient
public import CFSG.Quasithin.Chapter4.Section02.Unitary.RankTwoExclusions

/-!
# The unitary quotient in the original odd-actor pushing-up pair

Failure of uniqueness for L_A constructs the actual C.2.8 configuration.
Its normal intersection residual Y = (L ∩ H)∞ inherits the original
G₂(2)′ quotient via the literal quotient map. In particular Y, its span,
and every nontrivial escaping component action have three-rank at least
two. The ordinary and constrained binary rank-two exclusions therefore
apply to the same selected pair.

The source hypotheses supply covering uniqueness for LT; no uniqueness
of L_A, local row recognition or flag transport is assumed. Recognition
of the remaining rows, the Rudvalis flag geometry, and final odd-normalizer
control remain with qt-d-13316-source. Only the original earlier structural
12.2 input is used here, with final discharge at qt-theorem-d.

Source: Aschbacher–Smith 4.2.12–13 and 4.4.5–6, pp.610–612,620,
and the original 13.3.16 application, pp.893–896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual odd actor supplies a marked C.2.8 pair with no new local
premises; the residual and all its escaping actions retain three-rank two. -/
theorem unitary_original_oddActorResidual_pushingUp (s : Context T L V)
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
      (Y.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
      (∃ e : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived,
        ∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
          s.quotient (QuotientGroup.mk' (pCore 2 L)
            ⟨y.val,((map_subtype_le _).trans inf_le_left) y.property⟩)) ∧
      2 ≤ primeRank 3 Y ∧
      (∀ (K : Subgroup H), K.IsCComponent → IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H →
        2 ≤ primeRank 3 (coreCentralActorImage K (Y.subgroupOf H))) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hC,hn,⟨e,he⟩,hmark⟩ :=
    chosen_oddActorResidual_C28_quotient h12.toHypothesis1221 s.chosen A
      hAN hcomm hodd hAV hu hnot
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let eY := e.trans s.quotient
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y := le_antisymm
    (conjugateSpanBy_le le_rfl ((normal_subgroupOf_iff_le_normalizer hC.component_le).mp hn))
    (le_conjugateSpanBy _ _)
  refine ⟨J,H,S,hpush,hH,hJH,hlt,hC,hn,⟨eY,fun y => congrArg s.quotient (he y)⟩,
    ChapterC.HypothesisC28.unitary_seed_threeRank eY,?_,hmark⟩
  intro K hK hq hout
  have hr := hC.unitary_constrained_action_threeRank hn eY K hK hq hout
  change 2 ≤ primeRank 3 (coreCentralActorImage K
    ((conjugateSpanBy Y (H ⊓ normalizer (L : Set G))).subgroupOf H)) at hr
  rwa [hspan] at hr

open Chapter1.RadicalExclusions.ModelReduction

/-- The four binary rank-two exclusions apply to the actual intersection
residual from the original pushing-up pair. Neither a quotient marking nor
relative normality of that residual is an additional input. -/
theorem unitary_original_pushingUp_rankTwo_exclusions (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) {F : Type*} [Field F] [Finite F] [CharP F 2] :
    (IsComponent H K →
      (¬ Nonempty (K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)) ∧
      (2 < Nat.card F → ¬ Nonempty (K ⧸ center K ≃* Atlas.G2.Model F))) ∧
    (K.IsCComponent → IsQuasisimple (K ⧸ pCore 2 K) →
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H →
      generalizedFitting K = pCore 2 K → 4 ≤ Nat.card F →
      (¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F)) ∧
      (¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
        Atlas.G2.Model F))) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,e,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  let a := e.trans s.quotient
  constructor
  · intro hK
    exact ⟨fun ⟨f⟩ => hc.no_unitary_ordinary_sp4 a K hK f,
      fun hF ⟨f⟩ => hc.no_unitary_ordinary_g2 a K hK f hF⟩
  · intro hK hq hout hf hF
    exact ⟨fun ⟨f⟩ => hc.no_unitary_constrained_sp4 hn a K hK hq hout hf f hF,
      fun ⟨f⟩ => hc.no_unitary_constrained_g2 hn a K hK hq hout hf f hF⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
