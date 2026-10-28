module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport

/-!
# The two centralizer-action contradictions

The extension calculation puts V in U_L C_WL(L). If Y_C centralizes U_L,
then the moved plane V₂ lies in C_WL(L). If Y_C acts without fixed points
on the doubled natural U_L, then its fixed plane V₁ lies in C_WL(L).
The natural coordinates prove the directness needed in the second case.
Both conclusions contradict the corresponding source normalizer bound
for an outside component.

The explicit `CentralizerActionCases` contract keeps the doubled natural
coordinates and actual commutator and fixed-subgroup identities. It asserts
no existence. Its source producer must supply these alternatives, the
natural moving quotient and the radical involution; the fixed-space
containment itself is proved here. S-normalization of L is never assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.23,
the hypothetical centralizing branch on printed p.1128.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension
variable {G : Type*} [Group G]

private theorem sup_factorization {W U F : Subgroup G} [IsMulCommutative W]
    (hUW : U ≤ W) (hFW : F ≤ W) {w : G} (hw : w ∈ U ⊔ F) :
    ∃ u ∈ U, ∃ f ∈ F, u * f = w := by
  have hwW : w ∈ W := sup_le hUW hFW hw
  have hw' : (⟨w, hwW⟩ : W) ∈ U.subgroupOf W ⊔ F.subgroupOf W := by
    rw [← subgroupOf_sup hUW hFW]
    exact hw
  obtain ⟨u, hu, f, hf, he⟩ := mem_sup_of_normal_left.mp hw'
  exact ⟨u, hu, f, hf, congrArg Subtype.val he⟩

private theorem commutator_sup_le_fixed {W U F A : Subgroup G} [IsMulCommutative W]
    (hUW : U ≤ W) (hFW : F ≤ W) (hUC : U ≤ centralizer (A : Set G))
    (hAF : A ≤ normalizer (F : Set G)) : ⁅U ⊔ F, A⁆ ≤ F := by
  have hWF : W ≤ normalizer (F : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro w hw f hf
    exact congrArg Subtype.val (mul_comm (⟨f, hFW hf⟩ : W) ⟨w, hw⟩)
  apply commutator_le.mpr
  intro w hw a ha
  obtain ⟨u, hu, f, hf, rfl⟩ := sup_factorization hUW hFW hw
  have hfa : ⁅f, a⁆ ∈ F :=
    le_normalizer_iff_commutator_le_left.mp hAF (commutator_mem_commutator hf ha)
  have hua : ⁅u, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hUC hu a ha).symm)
  rw [commutatorElement_mul_left_eq_conj_mul, hua, mul_one]
  exact (hWF (hUW hu) _).mp hfa

private theorem fixed_sup_le_fixed_factor {W U F A : Subgroup G} [IsMulCommutative W]
    (hUW : U ≤ W) (hFW : F ≤ W) (hAU : A ≤ normalizer (U : Set G))
    (hAF : A ≤ normalizer (F : Set G)) (hd : Disjoint U F)
    (hfree : U ⊓ centralizer (A : Set G) = ⊥) :
    (U ⊔ F) ⊓ centralizer (A : Set G) ≤ F := by
  rintro w ⟨hw, hwC⟩
  obtain ⟨u, hu, f, hf, huf⟩ := sup_factorization hUW hFW hw
  have huC : u ∈ centralizer (A : Set G) := by
    intro a ha
    have hwu : a * (u * f) * a⁻¹ = u * f := by
      rw [huf]
      exact mul_inv_eq_iff_eq_mul.mpr (hwC a ha)
    have hprod : (u⁻¹ * (a * u * a⁻¹)) * (a * f * a⁻¹) = f := by
      calc _ = u⁻¹ * (a * (u * f) * a⁻¹) := by group
           _ = u⁻¹ * (u * f) := by rw [hwu]
           _ = f := by group
    have hF : u⁻¹ * (a * u * a⁻¹) ∈ F := by
      rw [eq_mul_inv_iff_mul_eq.mpr hprod]
      exact F.mul_mem hf (F.inv_mem ((hAF ha f).mp hf))
    have hU : u⁻¹ * (a * u * a⁻¹) ∈ U :=
      U.mul_mem (U.inv_mem hu) ((hAU ha u).mp hu)
    have he : u⁻¹ * (a * u * a⁻¹) = 1 := hd.le_bot ⟨hU, hF⟩
    have hfix : a * u * a⁻¹ = u := (inv_mul_eq_one.mp he).symm
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hu1 : u = 1 := hfree.le ⟨hu, huC⟩
  rw [hu1, one_mul] at huf
  exact huf ▸ hf

variable (d : LocalData G) (L : Subgroup G)
  [(actionKernel d L).Normal] [IsElementaryAbelian 2 (d.componentSpan L)]
  (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
  (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G))
  (e : (L ⧸ pCore 2 L) ≃* SL)

/-- Actual natural coordinates make U_L disjoint from the component fixed subgroup. -/
theorem copies_disjoint_component_fixed {m : ℕ}
    (copies : Copies (moving (componentRepresentation d L hN hcore e)).toRepresentation m) :
    Disjoint (spanCommutator d L) (d.componentSpan L ⊓ centralizer (L : Set G)) := by
  have hd := (disjoint_iff_fixedMoving_eq_bot (componentRepresentation d L hN hcore e)).mpr
    copies.fixed_eq_bot
  rw [fixedSpace_eq_centralizer, moving_eq_spanCommutator] at hd
  have hUW : spanCommutator d L ≤ d.componentSpan L :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy d.V L)
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro w hw
  let v : Additive (d.componentSpan L) := Additive.ofMul ⟨w, hUW hw.1⟩
  have hv : v ∈ subgroupSpace d L (centralizer (L : Set G)) ⊓
      subgroupSpace d L (spanCommutator d L) := ⟨hw.2.2, hw.1⟩
  have hz : v = 0 := hd.le_bot hv
  exact congrArg (fun x : Additive (d.componentSpan L) => (x.toMul : G)) hz


/-- The actual centralizer action alternatives. The doubled branch retains
its coordinates, full displacement, and vanishing fixed subgroup. Producing
this data is a local representation problem, not an order-three assumption. -/
def CentralizerActionCases : Prop :=
  ⁅spanCommutator d L, YC d L⁆ = ⊥ ∨
    (Nonempty (Copies (moving (componentRepresentation d L hN hcore e)).toRepresentation 2) ∧
      ⁅spanCommutator d L, YC d L⁆ = spanCommutator d L ∧
      spanCommutator d L ⊓ centralizer (YC d L : Set G) = ⊥)

/-- Either centralizer-action possibility contradicts the two source plane
normalizer bounds. The span containment is derived from the representation
and a radical involution in this theorem. -/
theorem nontrivial_of_module_and_plane_actions [Finite G]
    (houtside : ¬ L ≤ d.M)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : L.pCoreIn 2 ≤ d.R)
    {m : ℕ}
    (q : ModuleQuotient (moving (componentRepresentation d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e)).toRepresentation m)
    (l : L) (hlR : (l : G) ∈ d.R)
    (ht : e (QuotientGroup.mk l) ^ 2 = 1) (hne : e (QuotientGroup.mk l) ≠ 1)
    (hYL : d.Yplus ≤ normalizer (L : Set G))
    (hcases : CentralizerActionCases d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e)
    (hplanes : ⁅d.V, YL d L⁆ = ⊥ →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
        d.V₁ ≤ centralizer (YC d L : Set G) ∧ ⁅d.V₂, YC d L⁆ = d.V₂) :
    ⁅d.V, YL d L⁆ ≠ ⊥ := by
  intro hcentral
  obtain ⟨hN1, hN2, hC1, hmove2⟩ := hplanes hcentral
  have hV := V_le_spanCommutator_sup_centralizer d L hN e hR hcoreR q l hlR ht hne
  let F := d.componentSpan L ⊓ centralizer (L : Set G)
  have hUW : spanCommutator d L ≤ d.componentSpan L :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy d.V L)
  have hCY : YC d L ≤ d.Yplus := (ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left
  have hCL : YC d L ≤ normalizer (L : Set G) := hCY.trans hYL
  have hCW : YC d L ≤ normalizer (d.componentSpan L : Set G) :=
    hCY.trans (le_sup_right.trans hN)
  have hCF : YC d L ≤ normalizer (F : Set G) :=
    (le_inf hCW (hCL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  rcases hcases with htrivial | ⟨⟨copies⟩, _, hfree⟩
  · have hbound : ⁅spanCommutator d L ⊔ F, YC d L⁆ ≤ F :=
      commutator_sup_le_fixed hUW inf_le_left
        (commutator_eq_bot_iff_le_centralizer.mp htrivial) hCF
    have hV2 : d.V₂ ≤ F := by
      rw [← hmove2]
      exact (commutator_mono ((d.action.plane_le _).trans hV) le_rfl).trans hbound
    exact houtside ((le_centralizer_iff.mp (hV2.trans inf_le_right)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hN2))
  · have hCU : YC d L ≤ normalizer (spanCommutator d L : Set G) := by
      intro a ha
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [spanCommutator, map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hCW ha),
        mem_normalizer_iff_map_conj_eq.mp (hCL ha)]
    have hd := copies_disjoint_component_fixed d L hN
      (core_centralizes_span d L hcoreR (hR.le.trans inf_le_right)) e copies
    have hbound : (spanCommutator d L ⊔ F) ⊓ centralizer (YC d L : Set G) ≤ F :=
      fixed_sup_le_fixed_factor hUW inf_le_left hCU hCF hd hfree
    have hV1 : d.V₁ ≤ F :=
      (le_inf ((d.action.plane_le _).trans hV) hC1).trans hbound
    exact houtside ((le_centralizer_iff.mp (hV1.trans inf_le_right)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hN1))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

end
