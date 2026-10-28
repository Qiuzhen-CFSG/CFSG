module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryQuotient
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SpanProjection
public import Theory.Representation.SL2.MovedElementaryDegree

/-!
# The full moved module before ordinary normalizer identification

The actual full module survives the central quotient, stays elementary and
fully moved, and is normalized by the unchanged full Sylow. Its original
PSL₂(2ⁿ) quotient forces at least 2²ⁿ elements, hence the model order divisor
2³ⁿ(2²ⁿ−1). SourceSelectionOrdinaryCatalogue uses these bounds in its remaining
carrier cases. No full-normalizer equality or identification with chosen V
is used.

Source: Aschbacher–Smith C.3.1, pp.149–151, E.2.13(4), p.225, and 4.3.6, p.614.
This extends OrdinaryRecognitionModule to the original OutsideChoice.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (c : OutsideChoice T L) (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (K : Subgroup c.H) (ho : IsComponent c.H K)
  (hLK : L ≤ K.map c.H.subtype)
  (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
include D h ho hLK hout hKN
open ChapterA.Section02 ChapterA.Section03.SourceEmbeddings FiveLocalFF ClassificationModels

/-- The full module's image, its original local and Sylow actions, and the
rank-one lower bound in every actual central-quotient model. -/
theorem ordinary_model_module_data
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J) :
    let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    ∃ (S : Sylow 2 J) (E : Subgroup J), IsElementaryAbelian 2 E ∧
      (S : Subgroup J) ≤ normalizer (B : Set J) ∧
      (S : Subgroup J) ≤ normalizer (E : Set J) ∧
      E ≤ ((c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))).pCoreIn 2 ∧
      ⁅E,B⁆ = E ∧ 2 ^ (2*n) ≤ Nat.card E := by
  let W := c.ordinaryModule
  let WH := W.subgroupOf c.H
  let WK := WH.subgroupOf K
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  let E := WK.map f
  have hWL : W ≤ L := by simpa only [c.ordinary_span_eq] using (c.c28 D h).module_le
  have hLH : L ≤ c.H := c.contains
  have hWH : W ≤ c.H := hWL.trans hLH
  have hWK : WH ≤ K := (subgroupOf_mono c.H hWL).trans (c.ordinaryLocal_le hLK)
  have hWA : WK ≤ (c.ordinaryLocal K) := subgroupOf_mono K (subgroupOf_mono c.H hWL)
  have hEB : E ≤ B := map_mono hWA
  let := (c.c28 D h).module_elementary
  let : IsElementaryAbelian 2 WH := IsElementaryAbelian.subgroupOf hWH
  let : IsElementaryAbelian 2 WK := IsElementaryAbelian.subgroupOf hWK
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hmH : WH = ⁅WH,L.subgroupOf c.H⁆ := by
    apply map_injective c.H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hLH]
    simpa only [c.ordinary_span_eq] using (c.c28 D h).module_commutator
  have hmK : WK = ⁅WK,(c.ordinaryLocal K)⁆ := by
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,
      map_subgroupOf_eq_of_le (c.ordinaryLocal_le hLK)]
    exact hmH
  have hm : E = ⁅E,B⁆ := by rw [←map_commutator,←hmK]
  have hne : E ≠ ⊥ := by
    intro he
    have hk : f.ker = center K := by
      ext x
      change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
      rw [←map_one e,e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hz : WK ≤ center K := hk ▸ (map_eq_bot_iff WK).mp he
    apply (c.c28 D h).ordinary_module_not_centralizes K ho
    intro w hw k hk
    exact congrArg (fun x : K => (x : c.H))
      (mem_center_iff.mp (hz (show (⟨w,hWK hw⟩ : K) ∈ WK from hw)) ⟨k,hk⟩)
  obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have hTR : (T : Subgroup G) ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
      le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := Section02.Unitary.fullModule_map L
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) (MulAut.conj t)
    have hL : L.map (MulAut.conj t).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_component ht)
    have hR : ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj t).toMonoidHom =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := mem_normalizer_iff_map_conj_eq.mp (hTR ht)
    rw [hL,hR] at he
    exact he
  have hPN : (P : Subgroup K) ≤ normalizer (WK : Set K) := by
    rw [hP]
    intro p hp w
    exact hTW hp.1 ((w : c.H) : G)
  let U := E.subgroupOf B
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEB
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.ge)
  have hUcore : U ≤ pCore 2 B := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hEcore : E ≤ B.pCoreIn 2 := by
    rw [←map_subgroupOf_eq_of_le hEB]
    exact map_mono hUcore
  have hPB : (P : Subgroup K) ≤ normalizer ((c.ordinaryLocal K) : Set K) := by
    rw [hP]
    exact (c.ordinary_component_sylow_normalizes_local D K)
  refine ⟨S,E,inferInstance,(map_mono hPB).trans ((c.ordinaryLocal K).le_normalizer_map f),
    (map_mono hPN).trans (WK.le_normalizer_map f),hEcore,hm.symm,?_⟩
  let := (c.ordinaryLocal_perfect h K hLK)
  let : Group.IsPerfect B := Group.IsPerfect.map f
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact Representation.SL2.moved_subgroup_card_bound B E hEB hne hm.symm
    (b.trans (Theory.PSL2.sl2QuotientEquiv F).symm) (by omega : n ≠ 0) hF

omit hout hKN in
private theorem local_card
     {J : Type*} [Group J] [Finite J]
    (e : (K ⧸ center K) ≃* J) {n : ℕ}
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    Nat.card (B ⧸ pCore 2 B) = 2^n * ((2^n)^2-1) := by
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  dsimp only
  rw [Nat.card_congr b.toEquiv,←Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
    GorensteinWalter.sl2_card_formula,hF]

/-- The fully moved elementary layer supplies its two-part in addition to
that of the unchanged rank-one quotient. -/
theorem ordinary_model_moved_order_dvd
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J) :
    2^(3*n) * ((2^n)^2-1) ∣ Nat.card J := by
  let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  obtain ⟨_,E,hE,_,_,hEcore,_,hb⟩ := c.ordinary_model_module_data D h K ho hLK hout hKN hn hpsl e
  let := hE
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnk : 2*n ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk ▸ hb)
  have hdE : 2^(2*n) ∣ Nat.card E := hk ▸ pow_dvd_pow 2 hnk
  have hdcore : 2^(2*n) ∣ Nat.card (pCore 2 B) := by
    have hc := hdE.trans (card_dvd_of_le hEcore)
    change 2^(2*n) ∣ Nat.card ((pCore 2 B).map B.subtype) at hc
    rwa [card_map_of_injective B.subtype_injective] at hc
  have hdB : 2^(2*n) * (2^n * ((2^n)^2-1)) ∣ Nat.card B := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),c.local_card D h K ho hLK e hpsl,
      mul_comm (2^n * ((2^n)^2-1))]
    exact Nat.mul_dvd_mul hdcore dvd_rfl
  have hd := hdB.trans B.card_subgroup_dvd_card
  rw [←mul_assoc,←pow_add,show 2*n+n=3*n by omega] at hd
  exact hd

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
