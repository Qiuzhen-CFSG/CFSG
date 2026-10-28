module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalOneSidedAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryCentralizer
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex


/-!
# Reducedness and the offender on the literal field-plane quotient

For a field plane U in the original natural layer B, the arranged Sylow
subgroup of H = C_G(U) acts on B either trivially or as the field involution.
Its displacement lies in U, so the image of B in H/U is Sylow-central.
The elementary H-closure therefore gives a reduced subgroup of H/U.
Its faithful conjugation image has trivial two-core.

In the contrary one-sided configuration of 6.2.7, the actual conjugate
layer has image of order four. The fixed index four already proved on
its elementary closure gives the offender inequality on the literal
quotient. The constructed faithful representation retains the original
quotient coordinates and relative centralizer kernel.

The companion Chapter 12 module applies these results to [R₂(LT),L].
The component exclusions and graph escape are subsequent steps; no
LocalAnalysis, later recognition, or abstract module replacement is used.

Source: Aschbacher--Smith, 6.2.4(4) and 6.2.7, printed pp.680,682--683;
the Sylow-central closure argument is B.2.13--14, printed pp.78--79.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem field_centralizer_commutator
    {L M B U : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (P : Subgroup G) (hPL : P ≤ normalizer (L : Set G))
    (hPB : P ≤ normalizer (B : Set G)) :
    ⁅P ⊓ centralizer (U : Set G), B⁆ ≤ U := by
  have hnat := hnatural
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, htM, htB, hU, K, _, _, _, hK, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, _⟩ := field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    let v : B := ⟨u, (hU.le u.property).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le u.property).2
  have hsquare (b : B) : B.normalizerMonoidHom ⟨t, htB⟩
      (B.normalizerMonoidHom ⟨t, htB⟩ b) = b := by
    apply Subtype.ext
    have hh := congrArg (fun v => (f.symm (Multiplicative.ofAdd v) : G)) (hi (f b).toAdd)
    rw [vectorActor_coe, vectorActor_coe] at hh
    change (t : G) * ((t : G) * (b : G) * (t : G)⁻¹) * (t : G)⁻¹ = b
    simpa only [ofAdd_toAdd, f.symm_apply_apply] using hh
  apply commutator_le.mpr
  intro r hr b hb
  rcases field_fixedSpace_actor_dichotomy hnat t htB hU hUne
      ⟨K, inferInstance, inferInstance, inferInstance, hK, a, σ, hσ, hσsq, hσact⟩
      ⟨r, hPL hr.1⟩ (hPB hr.1) hr.2 with he | he
  · have hc := congrArg (fun E : MulAut B => (E ⟨b,hb⟩ : G)) he
    have hc' : r * b * r⁻¹ = b := hc
    rw [commutatorElement_def, hc', mul_inv_cancel]
    exact U.one_mem
  · have hc := congrArg (fun E : MulAut B => (E ⟨b,hb⟩ : G)) he
    have hc' : r * b * r⁻¹ = (t : G) * b * (t : G)⁻¹ := hc
    rw [commutatorElement_def, hc']
    let E := B.normalizerMonoidHom ⟨t, htB⟩
    let v : B := E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹
    have hv : E v = v := by
      change E (E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹) = E ⟨b,hb⟩ * (⟨b,hb⟩ : B)⁻¹
      rw [map_mul, map_inv, hsquare]
      have hpow (x : B) : x⁻¹ = x := by
        apply inv_eq_of_mul_eq_one_left
        apply Subtype.ext
        change (x : G) * (x : G) = 1
        simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property
      rw [hpow, hpow]
      exact mul_comm _ _
    have hvU : (v : G) ∈ U := by
      rw [hU]
      refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hv' : (t : G) * (v : G) * (t : G)⁻¹ = v := congrArg Subtype.val hv
      exact (mul_inv_eq_iff_eq_mul.mp hv').symm
    exact hvU

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Reducedness on the literal field-plane quotient closure. -/
theorem reduced_space
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    {U : Subgroup G}
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : 4 ≤ Nat.card U) : IsPReduced 2 (space (layer L R) U) := by
  let := h.layer_elementary
  let B := layer L R
  let H := Centralizer U
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hUne : U ≠ ⊥ := by intro he; rw [he, card_bot] at hUc; omega
  have hUB : U ≤ B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le hUB)
  have hML := (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  obtain ⟨P, _, hBP, hPL, hPB, _, hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L M B U n h.sylow_normalizes_layer hE.normalizer_le hML hE.ti hnat hfield hUne
  obtain ⟨_, _, _, S, hS⟩ := field_fixedSpace_sylow_control hE
    (by have := h.n_gt_one; omega) hnat hML hfield hUne P hBP hPB hSyl
  let q := projection U
  let W := (B.subgroupOf H).map q
  let Sq := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 (B.subgroupOf H) := IsElementaryAbelian.subgroupOf hBH
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hJe := local_plane_closure_elementary h hnatural hE hfactor hUB hUc
  let : IsElementaryAbelian 2 (conjugateSpanBy B H) := hJe
  let : IsElementaryAbelian 2 ((conjugateSpanBy B H).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf (conjugateSpanBy_le_self hBH)
  have hWe : IsElementaryAbelian 2 (space B U) := by
    rw [← closure_image B U hBH]
    exact IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (normalClosure (W : Set (Ambient U))) := hWe
  apply isPReduced_normalClosure_of_sylow_central Sq W
  · apply map_mono
    intro b hb
    apply (mem_map_iff_mem H.subtype_injective).mp
    rw [hS]
    exact ⟨hBP hb, b.property⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨s, hs, rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact field_centralizer_commutator hnat hfield hUne (P : Subgroup G) hPL hPB
      (commutator_mem_commutator (hS ▸ mem_map_of_mem H.subtype hs) hb)

/-- The actual action image has trivial two-core. -/
theorem action_range_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    {U : Subgroup G}
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : 4 ≤ Nat.card U) :
    pCore 2 (action (layer L R) U).range = ⊥ := by
  let W := space (layer L R) U
  let f : Ambient U →* MulAut W := MulAut.conjNormal
  have hred := reduced_space h hnatural hE hfactor hfield hUc
  have hr : (action (layer L R) U).range = f.range := by
    rw [action, MonoidHom.range_comp,
      (projection U).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  rw [hr]
  let e : (Ambient U ⧸ centralizer (W : Set (Ambient U))) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (MulAut.conjNormal_ker_eq_centralizer W).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  rw [← pCore_map_iso 2 e, hred.quotient_pCore_eq_bot, Subgroup.map_bot]

/-- The actual conjugate image is an offender on the faithful original section. -/
theorem exists_faithful_offender
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    letI := (reduced_space h hnatural hE hfactor
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).2.1
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).1.ge).elementary
    let H := Centralizer U
    let J := conjugateSpanBy B H
    let π := (action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (action B U).range (Additive (space B U)))
      (c : Representation.BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ Representation.BinaryOffender.IsOffender ρ I ∧
      Nat.card I = 4 ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, projection U ⟨j, hj⟩ = ((c.coordinates j).toAdd.toMul : Ambient U) := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  obtain ⟨hUc, hfield, hJe, _, _, _, _, _, _, _⟩ :=
    local_one_sided_closure_geometry h hnatural hE hfactor g hBA hnon
  let := (reduced_space h hnatural hE hfactor hfield hUc.ge).elementary
  let W := space B U
  let f := action B U
  let π := f.rangeRestrict
  let I := (A.subgroupOf H).map π
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le inf_le_left)
  have hJH : J ≤ H := conjugateSpanBy_le_self hBH
  have hUJ : U ≤ J := inf_le_left.trans (le_conjugateSpanBy B H)
  let cJ : J →* W := (projection U |>.comp (inclusion hJH)).codRestrict W (by
    intro j
    change projection U ⟨j, hJH j.property⟩ ∈ space B U
    rw [← closure_image B U hBH]
    exact mem_map_of_mem (projection U) j.property)
  have hcJ : Function.Surjective cJ := by
    intro w
    have hw := w.property
    change (w : Ambient U) ∈ space B U at hw
    rw [← closure_image B U hBH] at hw
    obtain ⟨j, hj, he⟩ := hw
    exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  let ρ : Representation (ZMod 2) f.range (Additive W) := {
    toFun a := a.val.toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by ext v; rfl
    map_mul' := by intro a b; ext v; rfl }
  let c : Representation.BinaryConjugationSection H J U (ρ.comp π) := {
    section_le := hJH
    kernel_le := hUJ
    normalized := le_normalizer_conjugateSpanBy B H
    coordinates := {
      toFun j := Multiplicative.ofAdd (Additive.ofMul (cJ j))
      map_one' := cJ.map_one
      map_mul' := cJ.map_mul }
    onto := hcJ
    kernel_eq := by
      ext j
      change cJ j = 1 ↔ (j : G) ∈ U
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    equivariant := by
      intro a j
      apply Additive.toMul.injective
      apply Subtype.ext
      change projection U (a * ⟨j, hJH j.property⟩ * a⁻¹) = _
      simp only [map_mul, map_inv]
      rfl }
  have hIfour : Nat.card I = 4 := by
    rw [← card_map_of_injective (f := f.range.subtype) (K := I) f.range.subtype_injective,
      map_map]
    exact (layer_image_four h hnatural hE hfactor g hBA hnon).1
  have hIe : IsElementaryAbelian 2 I := by
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 (A.subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (le_centralizer_iff.mpr inf_le_right)
    exact IsElementaryAbelian.map _
  refine ⟨ρ, c, ?_, ?_, hIfour, fun j => ⟨hJH j.property, rfl⟩⟩
  · intro a b he
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    exact congrArg (fun k : Module.End (ZMod 2) (Additive W) =>
      (k (Additive.ofMul w)).toMul) he
  · apply Representation.BinaryConjugationSection.offender_of_section_index ρ π c
      A (centralizer (A : Set G))
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp le_rfl)).le.trans bot_le
    · exact ⟨by intro he; change I = ⊥ at he; rw [he, card_bot] at hIfour; contradiction, hIe⟩
    · rw [hIfour]
      exact (local_one_sided_closure_action_index h hnatural hE hfactor g hBA hnon).le

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
