module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.NaturalSpan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Submodule
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Orbit
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The literal natural submodule V_K and its core intersection

The actual Hall scalar spectrum makes the original flag line a field line
in compatible natural coordinates on V_H. Its residual span is therefore
a natural two-space, with the literal K-action retained. The omega-center
span identities identify it with V_K = ⟨(Z intersect P)^H⟩.

The counterexample application constructs the pair marking and its axis
from the preceding inputs, proves V_K ≤ P, and computes its order q² and
rank 2n. Its V-fixed subgroup is precisely V₁. Since O₂(LT) centralizes V,
this gives O₂(LT) intersect V_K = V₁. Both subgroups normalize each other,
so [O₂(LT),V_K] ≤ V₁. The argument retains q=4 and assumes no compatible
field structures on P and V.

Only the permitted preceding source action, flag and Cartan conclusions
remain explicit; qt-d-1222-shadow-common-core retains their final discharge.
The remaining original SL₃ block, covering-complement application and local
core identifications remain with qt-d-1222-shadow-common-identification.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774, second paragraph.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

omit [Finite G] in
private theorem natural_marking_congr {F : BinaryField} {W W' : Subgroup G}
    (h : W = W') (hn : outsideResidual H ≤ normalizer (W : Set G))
    (hn' : outsideResidual H ≤ normalizer (W' : Set G))
    (ρ : outsideResidual H → SL(2,F.Carrier))
    (e : W ≃* Multiplicative (Fin 2 → F.Carrier))
    (he : ∀ k w, (e (W.normalizerMonoidHom (inclusion hn k) w)).toAdd =
      (ρ k).val *ᵥ (e w).toAdd) :
    ∃ e : W' ≃* Multiplicative (Fin 2 → F.Carrier),
      ∀ k w, (e (W'.normalizerMonoidHom (inclusion hn' k) w)).toAdd =
        (ρ k).val *ᵥ (e w).toAdd := by
  subst W'
  exact ⟨e,he⟩

theorem source_line_span_natural
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    let W := conjugateSpanBy (f.Vi 0) H
    W ≤ omegaClosure T H ∧ W ⊓ centralizer (V : Set G) = f.Vi 0 ∧
    ∃ (b : SL(2,S.field.Carrier)) (e : W ≃* Multiplicative (Fin 2 → S.field.Carrier)),
      ∀ (k : outsideResidual H) (w : W),
        (e (W.normalizerMonoidHom
          (inclusion ((outsideResidual_le H).trans (le_normalizer_conjugateSpanBy _ _)) k) w)).toAdd =
        (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ (e w).toAdd := by
  let := source_residualQuotient_simple hmodel
  let := D.elementary
  obtain ⟨hcomm,hline⟩ := source_line_of_fixed_spaces cL f hu s cK A X hA hHall
    hX hAX hfixed hf
  obtain ⟨b,n,he⟩ := cK.compatibleSylowCoordinates hf s.outside.1.1.2
    s.moves_omega_center (D.le_sylow.trans s.outside.1.1.2) R hR
  have hcontain : f.Vi 0 ≤ omegaClosure T H ⊓ centralizer (V : Set G) :=
    le_inf hline ((D.centralQuotientPreimage_le _).trans V.le_centralizer)
  have htri := cK.cartan_lowerLeft_eq_zero b n he (f.Vi 0) (oddCartanPart A)
    hcontain (f.V_ne_bot 0) hcomm
  have hspan : AddSubgroup.closure (cartanScalarSet cK b (oddCartanPart A)) = ⊤ := by
    apply top_unique
    rw [←torusScalarSet_additive_closure S.field]
    exact AddSubgroup.closure_mono (Hall.source_torus_scalar_spectrum s cK A hA hHall b htri)
  have hcard : Nat.card (f.Vi 0) = Nat.card S.field.Carrier :=
    source_flag_line_card cL f rfl hfixed
  obtain ⟨E,hE,hfix,hEU⟩ := cK.fieldLine_of_cartan_span b n he (f.Vi 0)
    (oddCartanPart A) hcontain hcomm hcard hspan
  let π : outsideResidual H →* SL(2,S.field.Carrier) :=
    (MulAut.conj b).toMonoidHom.comp
      (cK.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  have hπ : Function.Surjective π :=
    (MulAut.conj b).surjective.comp
      (cK.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hW,hfixedW,e,heq⟩ := n.natural_span_of_line π hπ
    (cK.compatibleSylow_intertwines b n he) E hE hfix
  have hWdef : conjugateSpanBy (n.liftSpace E) (outsideResidual H) =
      conjugateSpanBy (f.Vi 0) H := by
    rw [hEU,line_span_eq_residual_span cL f s]
  refine ⟨hWdef ▸ hW,?_,?_⟩
  · exact (congrArg (fun W => W ⊓ centralizer (V : Set G)) hWdef.symm).trans
      (hfixedW.trans hEU)
  · refine ⟨b,?_⟩
    exact natural_marking_congr hWdef (le_normalizer_conjugateSpanBy _ _)
      ((outsideResidual_le H).trans (le_normalizer_conjugateSpanBy _ _))
      (fun k => b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹) e heq

/-- The original K-action on the literal source V_K. -/
@[expose] def pairNaturalSpanAction : outsideResidual H →* MulAut (pairNaturalSpan T V H h) :=
  (pairNaturalSpan T V H h).normalizerMonoidHom.comp
    (inclusion ((outsideResidual_le H).trans (le_normalizer_conjugateSpanBy _ _)))

theorem source_pair_natural_span
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    let W := pairNaturalSpan T V H h
    W = conjugateSpanBy (f.Vi 0) H ∧
    W ≤ pairCore V H h ∧ W ≤ omegaClosure T H ∧
    IsElementaryAbelian 2 W ∧ Nat.card W = (2 ^ S.field.degree) ^ 2 ∧
    Group.rank W = 2 * S.field.degree ∧
    W ⊓ centralizer (V : Set G) = f.Vi 0 ∧
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ W = f.Vi 0 ∧
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,W⁆ ≤ f.Vi 0 ∧
    ∃ (b : SL(2,S.field.Carrier)) (e : W ≃* Multiplicative (Fin 2 → S.field.Carrier)),
      ∀ (k : outsideResidual H) (w : W),
        (e (pairNaturalSpanAction k w)).toAdd =
        (b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val *ᵥ (e w).toAdd := by
  have hAL := hAX.trans (hX.1.trans inf_le_left)
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  obtain ⟨hcore,⟨c⟩⟩ := source_pair_recognition s hh hm hf hnot hmodel cK
    R hR A hA hHall hAL
  have hm2 := c.sl3_multiplicity s hh hz rfl (axis_card_mul_field s hmodel R hR) a hfixed
  have hcardB : Nat.card (axis V H) = (2 ^ S.field.degree) ^ 2 := by
    rw [c.axis_card s hh hz,hm2]
  have hB := source_axis_eq_plane a f
    (fun i U hd hU => hu i U hd (inf_le_left.trans hU))
    s p hc hfixed hf hmodel cK R hR hcardB
  have hw := pairNaturalSpan_eq_line_span a f hu s hh hf hk hB hfixed cK
    A X hA hHall hX hAX
  have hline := source_line_span_natural (.sl3 a) f hu s hfixed hf hmodel R hR cK
    A X hA hHall hX hAX
  obtain ⟨hW',hfix',b,e',he'⟩ := hline
  have hW := hw.le.trans hW'
  have hfix : pairNaturalSpan T V H h ⊓ centralizer (V : Set G) = f.Vi 0 := by
    rw [hw]
    exact hfix'
  obtain ⟨e,he⟩ := natural_marking_congr hw.symm
    ((outsideResidual_le H).trans (le_normalizer_conjugateSpanBy _ _))
    ((outsideResidual_le H).trans (le_normalizer_conjugateSpanBy _ _))
    (fun k => b * cK.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹) e' he'
  let W := pairNaturalSpan T V H h
  have hWP : W ≤ pairCore V H h := conjugateSpanBy_le inf_le_right
    (pairCore_normalized_by_local s hh hk hcore)
  have hWT := hW.trans (source_omegaClosure_le_sylow s)
  have hUW : f.Vi 0 ≤ W := by
    change f.Vi 0 ≤ pairNaturalSpan T V H h
    rw [hw]
    exact le_conjugateSpanBy _ _
  have hUQ : f.Vi 0 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (D.centralQuotientPreimage_le _).trans D.le_core
  have hQW : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ W = f.Vi 0 := by
    apply le_antisymm _ (le_inf hUQ hUW)
    exact (le_inf inf_le_right (inf_le_left.trans D.core_centralizes)).trans hfix.le
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,W⁆ ≤ f.Vi 0 := by
    rw [←hQW]
    refine le_inf ?_ ?_
    · apply le_normalizer_iff_commutator_le_left.mp
      exact (hWT.trans le_sup_right).trans
        ((L ⊔ (T : Subgroup G)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    · exact le_normalizer_iff_commutator_le_right.mp
        ((hQT.trans s.outside.1.1.2).trans (le_normalizer_conjugateSpanBy _ _))
  let := source_omegaClosure_elementary s
  let := IsElementaryAbelian.of_le (p := 2) hW
  have hcardW : Nat.card W = (2 ^ S.field.degree) ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → S.field.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin,S.field.card_eq]
  refine ⟨hw,hWP,hW,inferInstance,hcardW,?_,hfix,hQW,hcomm,b,e,he⟩
  let : CommGroup W := IsMulCommutative.instCommGroup
  have hcard : Nat.card W = 2 ^ (2 * S.field.degree) := by
    rw [hcardW,←pow_mul,Nat.mul_comm S.field.degree 2]
  apply le_antisymm (IsElementaryAbelian.rank_le_of_card_le W hcard.le)
  have hd := card_dvd_exponent_pow_rank' W
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 W))
  rw [hcard] at hd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.le_of_dvd (by positivity) hd)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
