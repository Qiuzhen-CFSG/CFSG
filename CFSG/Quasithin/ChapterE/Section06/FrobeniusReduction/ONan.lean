module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.Basic

/-!
# The genuine E.6 input to the regular cyclic module theorem

For the faithful automizer action, the displacement span is the binary
subspace corresponding to the actual subgroup commutator [V,X]. The proof
compares generators in both directions; the commutator convention is
[x,v] = x v x⁻¹ v⁻¹. The fixed-space identification then transports the
source direct product and regular action. Hypothesis E.6.1 identifies the
local and full normalizers of V, allowing relative image normality to pass
to the full fixed-space stabilizer. Finally, r < m excludes small involutions.

Thus `RegularCyclicSection.toInput` constructs every field of the published
module input from the earlier cyclic section, U ∈ Γ, and 1 < r < m.
It does not assert the existence of the normal-closure decomposition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
preceding E.6.24, printed p.255 (PDF p.266). The cited extension is
Aschbacher, J. Algebra 70 (1981), 10.4.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction

variable {G : Type*} [Group G] (V : Subgroup G) [IsElementaryAbelian 2 V]

/-- The binary subspace corresponding to S ∩ V. -/
def binarySubspace (S : Subgroup G) : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 (S.subgroupOf V).toAddSubgroup

/-- Group commutators and linear displacements define the same subspace. -/
theorem displacementSpan_inducedAutomizer (X : Subgroup G) (hX : X ≤ normalizer (V : Set G)) :
    Representation.RegularCyclicNormalClosure.displacementSpan (automizerRepresentation V)
      (inducedAutomizer V X) ⊤ = binarySubspace V ⁅V, X⁆ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨x, hx, rfl⟩, v, _, rfl⟩
    change (((automizerRepresentation V) (V.normalizerMonoidHom.rangeRestrict x) v - v).toMul : G) ∈ ⁅V, X⁆
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    change (x : G) * (v.toMul : G) * (x : G)⁻¹ * (v.toMul : G)⁻¹ ∈ ⁅V, X⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hx v.toMul.property
  · let D := Representation.RegularCyclicNormalClosure.displacementSpan
      (automizerRepresentation V) (inducedAutomizer V X) ⊤
    let S : Subgroup G := D.toAddSubgroup.toSubgroup.map V.subtype
    have hcomm : ⁅X, V⁆ ≤ S := by
      apply commutator_le.mpr
      intro x hx v hv
      let a := V.normalizerMonoidHom.rangeRestrict ⟨x, hX hx⟩
      let w : Additive V := Additive.ofMul ⟨v, hv⟩
      refine ⟨(automizerRepresentation V a w - w).toMul, ?_, ?_⟩
      · change automizerRepresentation V a w - w ∈ D
        exact Submodule.subset_span ⟨a, ⟨⟨x, hX hx⟩, hx, rfl⟩, w, Submodule.mem_top, rfl⟩
      · simp only [toMul_sub, div_eq_mul_inv, map_mul, map_inv]
        rfl
    intro v hv
    obtain ⟨w, hw, he⟩ := hcomm (commutator_comm V X ▸ hv)
    have : w = v.toMul := Subtype.ext he
    subst w
    exact hw



/-- The fixed space is the relative centralizer inside V. -/
theorem fixedSpace_eq_binarySubspace (X : Subgroup G)
    (hX : X ≤ normalizer (V : Set G)) :
    fixedSpace (automizerRepresentation V) (inducedAutomizer V X) =
      binarySubspace V (V ⊓ centralizer (X : Set G)) := by
  ext v
  exact (mem_fixedSpace_inducedAutomizer V X hX v).trans
    ⟨fun hv => ⟨v.toMul.property, hv⟩, fun hv => hv.2⟩

private def binarySubspaceOrderIso : Subgroup V ≃o Submodule (ZMod 2) (Additive V) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

private theorem binarySubspace_sup {R S : Subgroup G} (hR : R ≤ V) (hS : S ≤ V) :
    binarySubspace V (R ⊔ S) = binarySubspace V R ⊔ binarySubspace V S := by
  change binarySubspaceOrderIso V ((R ⊔ S).subgroupOf V) = _
  rw [Subgroup.subgroupOf_sup hR hS, OrderIso.map_sup]
  rfl

private theorem binarySubspace_inf (R S : Subgroup G) :
    binarySubspace V (R ⊓ S) = binarySubspace V R ⊓ binarySubspace V S := by
  ext v
  rfl

private theorem binarySubspace_bot : binarySubspace V ⊥ = ⊥ := by
  ext v
  change (v.toMul : G) = 1 ↔ v = 0
  exact ⟨fun h => congrArg Additive.ofMul (Subtype.ext h), fun h => by subst v; rfl⟩

private theorem binarySubspace_self : binarySubspace V V = ⊤ := by
  ext v
  exact iff_true_intro v.toMul.property

variable {V} {M U X : Subgroup G}

/-- The source internal direct product becomes a complementary pair of subspaces. -/
theorem RegularCyclicSection.module_split (h : RegularCyclicSection M V U X)
    (hUV : U ≤ V) :
    IsCompl (fixedSpace (automizerRepresentation V) (inducedAutomizer V X))
      (Representation.RegularCyclicNormalClosure.displacementSpan
        (automizerRepresentation V) (inducedAutomizer V X) ⊤) := by
  have hX := h.contained.trans (inf_le_left.trans inf_le_right)
  rw [displacementSpan_inducedAutomizer V X hX, fixedSpace_eq_binarySubspace V X hX,
    h.fixed]
  apply isCompl_iff.mpr
  constructor
  · rw [disjoint_iff, ← binarySubspace_inf, h.disjoint, binarySubspace_bot]
  · rw [codisjoint_iff, ← binarySubspace_sup V hUV (le_normalizer_iff_commutator_le_left.mp hX),
      h.spanning, binarySubspace_self]


private def sectionHom (hX : X ≤ normalizer (V : Set G)) : X →* inducedAutomizer V X :=
  (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hX)).codRestrict _
    (fun x => ⟨⟨x, hX x.property⟩, x.property, rfl⟩)

omit [IsElementaryAbelian 2 V] in
private theorem sectionHom_surjective (hX : X ≤ normalizer (V : Set G)) :
    Function.Surjective (sectionHom hX) := by
  rintro ⟨a, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Regularity passes from X to its actual automizer image. -/
theorem RegularCyclicSection.module_regular (h : RegularCyclicSection M V U X) :
    ∀ v ∈ Representation.RegularCyclicNormalClosure.displacementSpan
        (automizerRepresentation V) (inducedAutomizer V X) ⊤, v ≠ 0 →
    ∀ w ∈ Representation.RegularCyclicNormalClosure.displacementSpan
        (automizerRepresentation V) (inducedAutomizer V X) ⊤, w ≠ 0 →
    ∃! c : inducedAutomizer V X, automizerRepresentation V c v = w := by
  have hX := h.contained.trans (inf_le_left.trans inf_le_right)
  rw [displacementSpan_inducedAutomizer V X hX]
  intro v hv hne w hw hwe
  have hvne : (v.toMul : G) ≠ 1 := fun he =>
    hne (congrArg Additive.ofMul (Subtype.ext he))
  have hwne : (w.toMul : G) ≠ 1 := fun he =>
    hwe (congrArg Additive.ofMul (Subtype.ext he))
  obtain ⟨x, he, hu⟩ := h.regular _ hv hvne _ hw hwne
  refine ⟨sectionHom hX x, ?_, ?_⟩
  · exact congrArg Additive.ofMul (Subtype.ext he)
  · intro c hc
    obtain ⟨y, rfl⟩ := sectionHom_surjective hX c
    apply congrArg (sectionHom hX)
    apply hu
    exact congrArg (fun w : Additive V => (w.toMul : G)) hc

variable [Finite G]

/-- The moved dimension is the source corank r. -/
theorem RegularCyclicSection.moved_finrank (h : RegularCyclicSection M V U X)
    (hUV : U ≤ V) :
    Module.finrank (ZMod 2) (Representation.RegularCyclicNormalClosure.displacementSpan
      (automizerRepresentation V) (inducedAutomizer V X) ⊤) = subgroupCorank V U := by
  have hX := h.contained.trans (inf_le_left.trans inf_le_right)
  have hs := Submodule.finrank_add_eq_of_isCompl (h.module_split hUV)
  have hf := fixedCodim_add_finrank (automizerRepresentation V) (inducedAutomizer V X)
  rw [fixedCodim_inducedAutomizer V X hX, h.fixed] at hf
  omega

/-- Relative image normality gives normality in the full fixed-space stabilizer. -/
theorem RegularCyclicSection.normal_in_fixedSpace_stabilizer
    {K : GroupClass} {T : Sylow 2 G} (hE : HypothesisE61 K T M V)
    (h : RegularCyclicSection M V U X) (hUV : U ≤ V)
    (a : Automizer V)
    (ha : (fixedSpace (automizerRepresentation V) (inducedAutomizer V X)).map
      (automizerRepresentation V a) =
        fixedSpace (automizerRepresentation V) (inducedAutomizer V X)) :
    (inducedAutomizer V X).map (MulAut.conj a).toMonoidHom = inducedAutomizer V X := by
  have hX := h.contained.trans (inf_le_left.trans inf_le_right)
  have haf : (binarySubspace V U).map (automizerRepresentation V a) = binarySubspace V U := by
    rwa [fixedSpace_eq_binarySubspace V X hX, h.fixed] at ha
  obtain ⟨g, hg⟩ := a.property
  have hga : V.normalizerMonoidHom.rangeRestrict g = a := Subtype.ext hg
  have hgn : (g : G) ∈ normalizer (U : Set G) := by
    apply (mem_normalizer_iff).mpr
    intro u
    constructor
    · intro hu
      have hv : Additive.ofMul ⟨u, hUV hu⟩ ∈ binarySubspace V U := hu
      have hm := Submodule.mem_map_of_mem (f := automizerRepresentation V a) hv
      rw [haf, ← hga] at hm
      exact hm
    · intro hu
      have huv : g * u * g⁻¹ ∈ V := hUV hu
      have hv : Additive.ofMul ⟨g * u * g⁻¹, huv⟩ ∈ binarySubspace V U := hu
      rw [← haf] at hv
      obtain ⟨v, hv, he⟩ := hv
      rw [← hga] at he
      have he' : (g : G) * (v.toMul : G) * (g : G)⁻¹ = (g : G) * u * (g : G)⁻¹ :=
        congrArg (fun w : Additive V => (w.toMul : G)) he
      have he'' : (v.toMul : G) = u := mul_left_cancel (mul_right_cancel he')
      exact he'' ▸ hv
  have hlarge : inducedAutomizer V X ≤ inducedAutomizer V
      (localNormalizer M V ⊓ normalizer (U : Set G)) := by
    apply Subgroup.map_mono
    intro x hx
    exact ⟨h.contained hx |>.1,
      centralizer_le_normalizer _ (h.contained hx |>.2)⟩
  apply mem_normalizer_iff_map_conj_eq.mp
  apply (normal_subgroupOf_iff_le_normalizer hlarge).mp h.normal_image
  refine ⟨g, ?_, hga⟩
  exact ⟨hE.localNormalizer_eq.symm ▸ g.property, hgn⟩

/-- All module hypotheses follow from the genuine E.6 cyclic section and corank bounds. -/
theorem RegularCyclicSection.toInput {K : GroupClass} {T : Sylow 2 G}
    (hE : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (h : RegularCyclicSection M V U X)
    (hlower : 1 < subgroupCorank V U) (hupper : subgroupCorank V U < localM V) :
    Representation.RegularCyclicNormalClosure.Input
      (automizerRepresentation V) (inducedAutomizer V X) := by
  have hX := h.contained.trans (inf_le_left.trans inf_le_right)
  refine {
    faithful := automizerRepresentation_injective V
    nontrivial := ?_
    cyclic := ?_
    fixed_nontrivial := ?_
    split := h.module_split hU.1
    regular := h.module_regular
    normal_in_stabilizer := h.normal_in_fixedSpace_stabilizer hE hU.1
    moved_dimension_gt_one := by rw [h.moved_finrank hU.1]; exact hlower
    no_small_involutions := ?_ }
  · intro he
    have hc := fixedCodim_inducedAutomizer V X hX
    rw [h.fixed, he, fixedCodim, fixedSpace_bot] at hc
    have hz : Module.finrank (ZMod 2) (Additive V ⧸ (⊤ : Submodule (ZMod 2) (Additive V))) = 0 :=
      Module.finrank_eq_zero_of_subsingleton _ _
    rw [hz] at hc
    omega
  · let _ := h.cyclic
    exact isCyclic_of_surjective (sectionHom hX) (sectionHom_surjective hX)
  · intro he
    obtain ⟨u, hu, hune⟩ := U.bot_or_exists_ne_one.resolve_left hU.2.1
    have hv : Additive.ofMul ⟨u, hU.1 hu⟩ ∈
        fixedSpace (automizerRepresentation V) (inducedAutomizer V X) := by
      rw [fixedSpace_eq_binarySubspace V X hX, h.fixed]
      exact hu
    rw [he, Submodule.mem_bot] at hv
    exact hune (congrArg (fun w : Additive V => (w.toMul : G)) hv)
  · intro a ha
    rw [h.moved_finrank hU.1]
    exact hupper.trans_le (moduleM_le_involution (automizerRepresentation V) ha)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
