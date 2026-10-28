module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.PushingUp
public import CFSG.Quasithin.Chapter4.Section02.Unitary.ConstrainedExclusion

/-!
# Ordinary components in the original odd-actor counterexample

Apply the complete constrained-row exclusion to the literal residual
Y = (L ∩ H)∞ of the actual pushing-up pair. Its relative normality and
G₂(2)′ quotient are proved from the covering relation and original chosen
module. Thus every escaping C-component with quasisimple core quotient is
ordinary, and its central quotient has order divisible by 6048.

The final theorem applies this to the same selected pair from failure of
uniqueness of L_A. It retains its original Sylow section centralizer and
chosen-module marking. No constrained classification or model callback
remains. The ordinary-component recognition, Rudvalis flag geometry and
terminal odd-normalizer argument remain with qt-d-13316-source; the earlier
12.2 structural input retains its final discharge at qt-theorem-d.

Source: Aschbacher–Smith 4.2.12–13 and 4.4.5–6, pp.610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Actual consumer: the source covering relation supplies every quotient
and normality premise of the complete constrained-row exclusion. -/
theorem unitary_original_pushingUp_ordinary_component (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    IsComponent H K ∧ 6048 ∣ Nat.card (coreCentralQuotient K) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,e,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  let a := e.trans s.quotient
  exact ⟨hc.unitary_escaping_component_isComponent hn a K hK hq hout,
    hc.unitary_component_central_order_dvd a K hK hq hout⟩

/-- Failure of uniqueness selects the original pair and full module, with
all of its escaping quasisimple C-components now proved ordinary. -/
theorem unitary_original_oddActorResidual_ordinary_pair (s : Context T L V)
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
        IsComponent H K ∧ 6048 ∣ Nat.card (coreCentralQuotient K)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,⟨e,_⟩,_,_,hmark⟩ :=
    unitary_original_oddActorResidual_pushingUp s A hAN hcomm hodd hAV hnot
  exact ⟨J,H,S,hpush,hH,hJH,hlt,hc,fun K hK hq hout =>
    ⟨hc.unitary_escaping_component_isComponent hn e K hK hq hout,
      hc.unitary_component_central_order_dvd e K hK hq hout⟩,hmark⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
