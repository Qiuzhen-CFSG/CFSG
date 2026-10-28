module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourBorelSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Overlap
public import Theory.SpecificGroups.MinusExtraspecial.OvergroupOrder

/-!
# The full reduced beta endpoint and Borel in the field-four branch

The five singular points of the minus extraspecial core bound the order of
any self-centralizing-core overgroup by 3840. The reduced beta parabolic
contains the constructed order-1920 enlargement and has Sylow order 128;
its odd Sylow index excludes the larger order. Thus the enlargement is the
entire reduced endpoint, and its original Borel intersection is the full
reduced Borel.

Transport the established native J₂ comparison along these subgroup
identities. The resulting endpoint, Borel and Sylow maps satisfy both
inclusion squares and retain the original PSL₂(4) quotient representatives.
The possible extension from the reduced pair to the original full pair is
kept separate; the alpha endpoint and path arguments remain to be proved.
Source: DGS, Groups and Graphs (1985), (10.9), p.163, and the original
reduction, pp.95--96 and (15.1)--(15.3), pp.226--231.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourFullAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

open SuzukiContainment

/-- The beta enlargement is the full reduced endpoint, with its entire reduced Borel. -/
theorem original_bTwo_field_four_reduced_beta_equals_enlargement
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    P₀ L S 1 = enlargedEndpoint L S 1 ∧
      B₀ L S = enlargedEndpoint L S 1 ⊓ commonBorel L S ∧
      Nat.card (P₀ L S 1) = 1920 ∧ Nat.card (B₀ L S) = 384 := by
  let P := P₀ L S 1
  let X := enlargedEndpoint L S 1
  let T := (commonBorel L S).pCoreIn 2
  have hXP : X ≤ P := sup_le le_sup_left (le_sup_right.trans le_sup_right)
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite P := Finite.of_injective (inclusion (P₀_le h 1)) (inclusion_injective _)
  obtain ⟨hX,hT,hB,_⟩ := original_bTwo_field_four_beta_enlargement_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,⟨eQ⟩⟩ := original_bTwo_field_four_beta_recognition
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hN : (pCore 2 P).map P.subtype = (parabolic L S 1).pCoreIn 2 := by
    change (P₀ L S 1).pCoreIn 2 = _
    rw [P₀_eq_source h 1]
    exact reduced_parabolic_core h 1
  let eN : pCore 2 P ≃* MinusExtraspecial.Model :=
    (((pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hN)).trans eQ
  have hcP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
    let := (reduced_hypothesis h).finite_parabolic 1
    have hh := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      ((reduced_hypothesis h).characteristic_two 1)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (MulEquiv.subgroupCongr (P₀_eq_source h 1))).mpr hh
  have hd := MinusExtraspecial.card_dvd_of_self_centralizing_core (pCore 2 P) eN hcP
  have hx := relIndex_mul_relIndex (⊥ : Subgroup G) X P bot_le hXP
  rw [relIndex_bot_left,relIndex_bot_left,hX] at hx
  have hi : X.relIndex P ∣ 2 := by
    have hh : 1920 * X.relIndex P ∣ 1920 * 2 := by simpa only [hx] using hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 1920)).mp hh
  have hTP : T ≤ P := le_sup_right.trans le_sup_right
  have htcard := relIndex_mul_relIndex (⊥ : Subgroup G) T P bot_le hTP
  rw [relIndex_bot_left,relIndex_bot_left,hT] at htcard
  have hodd : ¬ 2 ∣ T.relIndex P := by
    simpa only [P,P₀_eq_source h 1,T,reducedSylow,twoCore,pCoreIn] using
      (reduced_hypothesis h).parabolic_odd_index 1
  have hP : Nat.card P = 1920 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · omega
    · have htidx : T.relIndex P = 30 := by omega
      exact (hodd (htidx ▸ (by decide : 2 ∣ 30))).elim
  have he : P = X := (eq_of_le_of_card_ge hXP (by rw [hP,hX])).symm
  have hB₀ : B₀ L S = X ⊓ commonBorel L S := by
    rw [←he]
    change B₀ L S = P₀ L S 1 ⊓ commonBorel L S
    rw [P₀_eq_source h 1,OriginalExtension.reduced_parabolic_inf_borel h 1,B₀_eq_source h]
  exact ⟨he,hB₀,hP,hB₀ ▸ hB⟩


local notation "Jβ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B
local notation "JS" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s

private theorem quotient_marking_transport
    {A X Y H : Type*} [Group A] [Group X] [Group Y] [Group H]
    (a : A →* X) (f : X ≃* Y)
    (eX : (X ⧸ pCore 2 X) ≃* H) (eA : (A ⧸ pCore 2 A) ≃* H)
    (ha : ∀ x : A, eX (QuotientGroup.mk' (pCore 2 X) (a x)) =
      eA (QuotientGroup.mk' (pCore 2 A) x)) :
    ∃ d : (Y ⧸ pCore 2 Y) ≃* H,
      ∀ x : A, d (QuotientGroup.mk' (pCore 2 Y) (f (a x))) =
        eA (QuotientGroup.mk' (pCore 2 A) x) := by
  let fq := QuotientGroup.congr (pCore 2 X) (pCore 2 Y) f (pCore_map_iso 2 f)
  refine ⟨fq.symm.trans eX,fun x => ?_⟩
  change eX (fq.symm (fq (QuotientGroup.mk' (pCore 2 X) (a x)))) = _
  exact (congrArg eX (fq.symm_apply_apply _)).trans (ha x)

private theorem reindex_marked_equiv
    {H C : Type*} [Group H] [Group C]
    {P X B Y T A : Subgroup G} {M MB MT : Subgroup H}
    (hP : P = X) (hB : B = Y)
    (hBP : B ≤ P) (hYX : Y ≤ X) (hTP : T ≤ P) (hTX : T ≤ X)
    (hAP : A ≤ P) (hAX : A ≤ X)
    (f : X ≃* M) (fB : Y ≃* MB) (fT : T ≃* MT)
    (hfB : ∀ b : Y, (fB b : H) = (f (inclusion hYX b) : H))
    (hfT : ∀ t : T, (fT t : H) = (f (inclusion hTX t) : H))
    (eX : (X ⧸ pCore 2 X) ≃* C) (eA : (A ⧸ pCore 2 A) ≃* C)
    (heX : ∀ a : A, eX (QuotientGroup.mk' (pCore 2 X) (inclusion hAX a)) =
      eA (QuotientGroup.mk' (pCore 2 A) a)) :
    ∃ (fP : P ≃* M) (fB₀ : B ≃* MB) (fT₀ : T ≃* MT),
      (∀ b : B, (fB₀ b : H) = (fP (inclusion hBP b) : H)) ∧
      (∀ t : T, (fT₀ t : H) = (fP (inclusion hTP t) : H)) ∧
      ∃ d : (M ⧸ pCore 2 M) ≃* C,
        ∀ a : A, d (QuotientGroup.mk' (pCore 2 M) (fP (inclusion hAP a))) =
          eA (QuotientGroup.mk' (pCore 2 A) a) := by
  obtain ⟨d,hd⟩ := quotient_marking_transport (inclusion hAX) f eX eA heX
  refine ⟨(MulEquiv.subgroupCongr hP).trans f,
    (MulEquiv.subgroupCongr hB).trans fB,fT,?_,?_,d,?_⟩
  · intro b
    exact hfB (MulEquiv.subgroupCongr hB b)
  · intro t
    exact hfT t
  · intro a
    exact hd a

/-- The complete reduced beta endpoint and Borel, with both inclusion squares
and the original local PSL₂(4) marking. -/
theorem original_bTwo_field_four_reduced_beta_borel_equiv
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ (f : P₀ L S 1 ≃* Jβ) (fB : B₀ L S ≃* JB)
      (fT : (commonBorel L S).pCoreIn 2 ≃* JS),
      (∀ b : B₀ L S, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion le_sup_right b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ t : (commonBorel L S).pCoreIn 2, (fT t : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion (le_sup_right.trans le_sup_right) t) : Sporadic.LeechRelated.J2.Carrier)) ∧
      ∃ d : (Jβ ⧸ pCore 2 Jβ) ≃* PSL(2,K),
        ∀ x : L 1, d (QuotientGroup.mk' (pCore 2 Jβ)
          (f (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x))) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x) := by
  obtain ⟨hP,hB,_,_⟩ := original_bTwo_field_four_reduced_beta_equals_enlargement
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨f,fT,fB,_,_,hfT,hfB⟩ := original_bTwo_field_four_beta_enlargement_borel_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,_,_,eX,heX,_⟩ := original_bTwo_field_four_beta_enlargement_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact reindex_marked_equiv hP hB le_sup_right inf_le_left
    (le_sup_right.trans le_sup_right) le_sup_right
    ((local_le_starredParabolic 1).trans le_sup_left)
    ((local_le_starredParabolic 1).trans le_sup_left) f fB fT hfB hfT eX e heX

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
