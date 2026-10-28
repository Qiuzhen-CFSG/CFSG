module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.Quotient
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder

/-!
# The second J4 involution centralizer

For the literal max1 seed `(xy)^14`, the full ambient centralizer equals the
local centralizer: the independently certified ambient upper bound matches
the local lower bound. Transport the actual elementary kernel, pair-stabilizer
quotient and faithful conjugation action along this inclusion equivalence.
The elementary kernel is self-centralizing, so the centralizer has no components.

The local calculation is independent of the ambient bound. Conditional
transport remains available, and the unconditional exports apply the proved bound.
Source: Aschbacher--Smith 16.1.5(9), 16.1.7, printed pp.1172--1173;
GLS3 Table 5.3i. This is an extension description, without a splitting assertion.
-/

@[expose] public section
noncomputable section
namespace Janko4.InvolutionCentralizers.Second
open Subgroup Cardinality Simplicity LocalStructure.MathieuSeedCentralizer Sporadic.Mathieu

abbrev ambientCentralizer : Subgroup Model :=
  ambientSeedCentralizer matrixA_mul_self matrixB_pow_four

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed localKernel

/-- A matching upper bound forces literal containment in max1. -/
theorem ambient_le_max1_of_card_le
    (hc : Nat.card ambientCentralizer ≤ 1816657920) :
    ambientCentralizer ≤ max1Subgroup matrixA_mul_self matrixB_pow_four :=
  ambientSeedCentralizer_le_max1_of_card_le _ _ hc

/-- Local and full centralizers coincide as subgroups of the original matrix group. -/
theorem ambient_eq_map_of_card_le
    (hc : Nat.card ambientCentralizer ≤ 1816657920) :
    ambientCentralizer = localCentralizer.map
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype := by
  apply le_antisymm
  · intro g hg
    let z : Local := ⟨g, ambient_le_max1_of_card_le hc hg⟩
    refine ⟨z, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp hg
  · exact map_localSeedCentralizer_le _ _

/-- The inclusion-induced equivalence, with only the ambient bound conditional. -/
def ambientEquivLocal_of_card_le
    (hc : Nat.card ambientCentralizer ≤ 1816657920) :
    ambientCentralizer ≃* localCentralizer :=
  (MulEquiv.subgroupCongr (ambient_eq_map_of_card_le hc)).trans
    (localCentralizer.equivMapOfInjective
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype_injective).symm

/-- The accepted intrinsic ambient bound discharges containment unconditionally. -/
theorem ambient_le_max1 :
    ambientCentralizer ≤ max1Subgroup matrixA_mul_self matrixB_pow_four :=
  ambient_le_max1_of_card_le ambientSeedCentralizer_card_le

def ambientEquivLocal : ambientCentralizer ≃* localCentralizer :=
  ambientEquivLocal_of_card_le ambientSeedCentralizer_card_le

/-- The inverse equivalence is the literal subgroup inclusion into the matrix model. -/
theorem ambientEquivLocal_symm_val (g : localCentralizer) :
    (ambientEquivLocal.symm g : Model) = (g.val : Model) := rfl

/-- The marked seed is an involution in the actual J4 carrier. -/
theorem seed_order : orderOf (seed : Model) = 2 := by
  obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.seed_fuses_second
    matrixA_mul_self matrixB_pow_four
  have ht : orderOf (word (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four) "ababb" ^ 5) = 2 :=
    Simplicity.involutionRepresentative_one_orderOf matrixA_mul_self matrixB_pow_four
  rw [hg] at ht
  exact ((MulAut.conj g).orderOf_eq (seed : Model)).symm.trans ht

/-- The full centralizer has the independently matching local and ambient order. -/
theorem ambient_card : Nat.card ambientCentralizer = 1816657920 :=
  Nat.le_antisymm ambientSeedCentralizer_card_le (ambientSeedCentralizer_card_ge _ _)

/-- Conditional full-centralizer transport of the actual local short exact sequence. -/
def ambientExtension_of_card_le
    (hc : Nat.card ambientCentralizer ≤ 1816657920) :
    GroupExtension kernel ambientCentralizer (MulAut M22) where
  inl := (ambientEquivLocal_of_card_le hc).symm.toMonoidHom.comp kernel.subtype
  rightHom := toAutM22.comp (ambientEquivLocal_of_card_le hc).toMonoidHom
  inl_injective := (ambientEquivLocal_of_card_le hc).symm.injective.comp kernel.subtype_injective
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change toAutM22 ((ambientEquivLocal_of_card_le hc)
        ((ambientEquivLocal_of_card_le hc).symm u.val)) = 1
      rw [(ambientEquivLocal_of_card_le hc).apply_symm_apply]
      exact SetLike.ext_iff.mp toAutM22_ker u.val |>.mpr u.property
    · intro hg
      have hk : (ambientEquivLocal_of_card_le hc) g ∈ kernel :=
        SetLike.ext_iff.mp toAutM22_ker _ |>.mp hg
      exact ⟨⟨_, hk⟩, (ambientEquivLocal_of_card_le hc).symm_apply_apply g⟩
  rightHom_surjective := toAutM22_surjective.comp (ambientEquivLocal_of_card_le hc).surjective

/-- The full literal centralizer is the actual E2048.Aut(M22) extension. -/
def ambientExtension : GroupExtension kernel ambientCentralizer (MulAut M22) :=
  ambientExtension_of_card_le ambientSeedCentralizer_card_le

/-- The full extension embeds exactly the original binary kernel matrices. -/
theorem ambientExtension_inl_val (u : kernel) :
    (ambientExtension.inl u : Model) = ((u.val : Local) : Model) :=
  ambientEquivLocal_symm_val u.val

/-- The faithful action exported above is the actual full-centralizer conjugation. -/
theorem ambientExtension_action (g : ambientCentralizer) (u : kernel) :
    ambientExtension.inl (autM22Action (ambientExtension.rightHom g) u) =
      g * ambientExtension.inl u * g⁻¹ := by
  apply ambientEquivLocal.injective
  simpa only [map_mul, map_inv, ambientExtension, ambientExtension_of_card_le,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ambientEquivLocal, MulEquiv.apply_symm_apply, Subgroup.subtype_apply] using
      autM22Action_apply (ambientEquivLocal g) u

/-- The kernel as an embedded normal subgroup of the full matrix centralizer. -/
abbrev ambientKernel : Subgroup ambientCentralizer := ambientExtension.rightHom.ker

/-- The full centralizer quotient is genuinely equivalent to native Aut(M22). -/
def ambientQuotientEquivAutM22 :
    (ambientCentralizer ⧸ ambientKernel) ≃* MulAut M22 :=
  QuotientGroup.quotientKerEquivOfSurjective ambientExtension.rightHom
    ambientExtension.rightHom_surjective

/-- The embedded full kernel is the image of the very same local E2048. -/
theorem ambientKernel_eq_map :
    ambientKernel = kernel.map ambientEquivLocal.symm.toMonoidHom := by
  change ambientExtension.rightHom.ker = _
  rw [← ambientExtension.range_inl_eq_ker_rightHom]
  change (ambientEquivLocal.symm.toMonoidHom.comp kernel.subtype).range = _
  rw [MonoidHom.range_comp, range_subtype]

theorem ambientKernel_elementary : IsElementaryAbelian 2 ambientKernel := by
  rw [ambientKernel_eq_map]
  let := kernel_elementary
  exact IsElementaryAbelian.map _

theorem ambientKernel_card : Nat.card ambientKernel = 2048 := by
  rw [ambientKernel_eq_map, card_map_of_injective ambientEquivLocal.symm.injective]
  exact kernel_card

/-- Self-centralization concerns the actual full-centralizer kernel. -/
theorem ambientKernel_selfCentralizing :
    centralizer (ambientKernel : Set ambientCentralizer) = ambientKernel := by
  ext g
  have hk (x : ambientCentralizer) : x ∈ ambientKernel ↔ ambientEquivLocal x ∈ kernel := by
    change toAutM22 (ambientEquivLocal x) = 1 ↔ _
    exact SetLike.ext_iff.mp toAutM22_ker _
  constructor
  · intro hg
    apply (hk g).mpr
    rw [← kernel_selfCentralizing]
    intro u hu
    have hc := hg (ambientEquivLocal.symm u)
      ((hk _).mpr (by rw [ambientEquivLocal.apply_symm_apply]; exact hu))
    simpa only [map_mul, ambientEquivLocal.apply_symm_apply] using congrArg ambientEquivLocal hc
  · intro hg u hu
    apply ambientEquivLocal.injective
    simp only [map_mul]
    exact kernel_selfCentralizing.ge ((hk g).mp hg) _ ((hk u).mp hu)

/-- No components occur in the full centralizer of the literal seed. -/
theorem ambient_no_component_of_card_le
    (hc : Nat.card ambientCentralizer ≤ 1816657920) (K : Subgroup ambientCentralizer) :
    ¬ Theory.GroupTheory.IsComponent ambientCentralizer K := by
  intro hK
  exact localCentralizer_no_component
    (K.map (ambientEquivLocal_of_card_le hc).toMonoidHom)
    (hK.map_equiv (ambientEquivLocal_of_card_le hc))

theorem ambient_no_component (K : Subgroup ambientCentralizer) :
    ¬ Theory.GroupTheory.IsComponent ambientCentralizer K :=
  ambient_no_component_of_card_le ambientSeedCentralizer_card_le K

end Janko4.InvolutionCentralizers.Second
