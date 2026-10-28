module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedSpace
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadElementary
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Core
public import Theory.GroupTheory.PCoreImage

/-!
# Transporting the hexad fixed space to the original extraspecial core

The original H → H/Q map, followed by its established full native action
marking, has kernel exactly Q. One design conjugator aligns every original
hexad preimage with the full native hexad stabilizer. The two-cores map onto
each other because the kernel is a two-group.

In the same quadratic coordinates, the original E₁ is exactly the full
preimage of this native fixed space. Total singularity gives exponent two;
cardinality 64 lifts to order 128 because the kernel is the central line.
The resulting source product E is elementary of order 2048 and normalized
by the original G₁,₃. All these conclusions reduce to the two standard-hexad
facts; no point-indexed preimage is substituted for the hexad preimage.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), proof of (4.6), p.598, DOI 10.1007/BF01232280.
The standard native calculation and later Thompson/normalizer recognition
remain to be discharged in this source family.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry LocalGeometry.LocalSubgroups
open M22TripleCover M22TripleCover.Ambient InvariantPoint M22ValueBound.Concrete
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e)) [IsExtraspecial 2 (core z)]

/-- The literal action map of the original H, with its kernel Q retained. -/
def coreNativeProjection : centralizer z →* actionGroup :=
  (coreAmbientHom h e X).comp (QuotientGroup.mk' (core z))

theorem coreNativeProjection_surjective : Function.Surjective (coreNativeProjection h e X) :=
  (coreAmbientHom_surjective h e X).comp (QuotientGroup.mk'_surjective (core z))

theorem coreNativeProjection_ker : (coreNativeProjection h e X).ker = core z := by
  rw [coreNativeProjection,MonoidHom.ker_comp_of_injective _ _
    (coreAmbientHom_injective h e X),QuotientGroup.ker_mk']

/-- A single native design conjugator aligns all original hexad stabilizers. -/
theorem originalPlaneHexad_native_image :
    ∃ b : m22DesignAut, ∀ B : Finset (Fin 22),
      (originalPlaneHexad e B).map (coreNativeProjection h e X) =
        nativeHexadStabilizer (b • B) := by
  obtain ⟨b,hb⟩ := original_point_marking h e X
  refine ⟨b,fun B => ?_⟩
  ext g
  obtain ⟨j,rfl⟩ := coreNativeProjection_surjective h e X g
  have hk : (coreNativeProjection h e X).ker ≤ originalPlaneHexad e B := by
    rw [coreNativeProjection_ker]
    exact (CubicLift.core_le e).trans (originalPlaneHexad_cubic_le e B)
  change j ∈ ((originalPlaneHexad e B).map (coreNativeProjection h e X)).comap
    (coreNativeProjection h e X) ↔ _
  rw [comap_map_eq_self hk]
  change CubicLift.projection e j ∈ designStabilizer B ↔
    pointAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) j)) • (b • B) = b • B
  rw [hb]
  have hl : CubicLift.projection e j ∈ designStabilizer B ↔
      designAutEquiv.symm (CubicLift.projection e j) • B = B := by
    change CubicLift.projection e j ∈
      (MulAction.stabilizer m22DesignAut B).map designAutEquiv.toMonoidHom ↔ _
    constructor
    · rintro ⟨a,ha,hae⟩
      rw [←hae,show designAutEquiv.toMonoidHom a = designAutEquiv a from rfl,
        MulEquiv.symm_apply_apply]
      exact ha
    · intro hj
      exact ⟨designAutEquiv.symm (CubicLift.projection e j),hj,
        designAutEquiv.apply_symm_apply _⟩
  rw [hl]
  change _ ↔ (b * designAutEquiv.symm (CubicLift.projection e j) * b⁻¹) • (b • B) = b • B
  rw [mul_smul,mul_smul,inv_smul_smul]
  exact (MulAction.injective b).eq_iff.symm

theorem originalPlaneHexad_twoCore_native_image (B B' : Finset (Fin 22))
    (he : (originalPlaneHexad e B).map (coreNativeProjection h e X) = nativeHexadStabilizer B') :
    ((originalPlaneHexad e B).pCoreIn 2).map (coreNativeProjection h e X) =
      (nativeHexadStabilizer B').pCoreIn 2 := by
  have hk : IsPGroup 2 (coreNativeProjection h e X).ker := by
    rw [coreNativeProjection_ker]
    exact IsPGroup.of_card h.core_card
  rw [map_pCoreIn_of_ker_isPGroup _ hk,he]

/-- Fixation in the native coordinates is exactly a central original commutator. -/
theorem coreNativeProjection_fixed_iff (g : centralizer z) (q : core z) :
    binaryAction (coreNativeProjection h e X g) ((corePointProjection h e X q).toAdd) =
      (corePointProjection h e X q).toAdd ↔ ⁅g,(q : centralizer z)⁆ ∈ center (centralizer z) := by
  change binaryAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) g))
      (coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) =
    coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ↔ _
  rw [←coreAmbientHom_intertwines,(coreNativeEquiv h e X).injective.eq_iff]
  change Additive.ofMul (coreQuotientAction h (QuotientGroup.mk' (core z) g)
    (QuotientGroup.mk' (center (core z)) q)) = Additive.ofMul
      (QuotientGroup.mk' (center (core z)) q) ↔ _
  rw [coreQuotientAction_mk]
  change QuotientGroup.mk' (center (core z)) (MulAut.conjNormal g q) =
    QuotientGroup.mk' (center (core z)) q ↔ _
  rw [←mul_inv_eq_one,←map_inv,←map_mul,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff,
    ←core_center_eq_centralizer_center h]
  change (MulAut.conjNormal g q * q⁻¹) ∈ center (core z) ↔
    ((MulAut.conjNormal g q * q⁻¹ : core z) : centralizer z) ∈ (center (core z)).map (core z).subtype
  exact (mem_map_iff_mem (core z).subtype_injective).symm

/-- The source E₁ is precisely the full preimage of the native hexad fixed space. -/
theorem originalHexadFixedCore_native_mem (B B' : Finset (Fin 22))
    (he : (originalPlaneHexad e B).map (coreNativeProjection h e X) = nativeHexadStabilizer B')
    (q : core z) :
    (q : centralizer z) ∈ originalHexadFixedCore h e X B ↔
      (corePointProjection h e X q).toAdd ∈ nativeHexadFixedSpace B' := by
  rw [originalHexadFixedCore_source,commutatorPreimage_eq_inf_comap_centralizer]
  change ((q : centralizer z) ∈ core z ∧
      QuotientGroup.mk' (center (centralizer z)) q.val ∈ Subgroup.centralizer
        (((originalPlaneHexad e B).pCoreIn 2).map (QuotientGroup.mk' (center (centralizer z))) : Set _)) ↔ _
  rw [and_iff_right q.property,mem_centralizer_iff_commutator_eq_one]
  have hi := originalPlaneHexad_twoCore_native_image h e X B B' he
  constructor
  · intro hq g hg
    obtain ⟨j,hj,rfl⟩ := hi.ge hg
    apply (coreNativeProjection_fixed_iff h e X j q).mpr
    have hh := hq _ (mem_map_of_mem (QuotientGroup.mk' (center (centralizer z))) hj)
    rw [←map_commutatorElement,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff] at hh
    exact hh
  · intro hq g hg
    obtain ⟨j,hj,rfl⟩ := hg
    have hh := (coreNativeProjection_fixed_iff h e X j q).mp
      (hq _ (hi.le (mem_map_of_mem _ hj)))
    rw [←map_commutatorElement,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    exact hh

/-- Equality of literal subgroups, rather than an abstract vector-space comparison. -/
theorem originalHexadFixedCore_native_preimage (B B' : Finset (Fin 22))
    (he : (originalPlaneHexad e B).map (coreNativeProjection h e X) = nativeHexadStabilizer B') :
    originalHexadFixedCore h e X B =
      (((nativeHexadFixedSpace B').toAddSubgroup.toSubgroup).comap
        (corePointProjection h e X)).map (core z).subtype := by
  apply le_antisymm
  · intro q hq
    have hqQ := originalHexadFixedCore_le h e X B hq
    exact ⟨⟨q,hqQ⟩,(originalHexadFixedCore_native_mem h e X B B' he ⟨q,hqQ⟩).mp hq,rfl⟩
  · rintro q ⟨u,hu,rfl⟩
    exact (originalHexadFixedCore_native_mem h e X B B' he u).mpr hu

/-- A singular native fixed space lifts to the actual elementary E₁. -/
theorem originalHexadFixedCore_elementary_of_native (B B' : Finset (Fin 22))
    (he : (originalPlaneHexad e B).map (coreNativeProjection h e X) = nativeHexadStabilizer B')
    (hs : ∀ v ∈ nativeHexadFixedSpace B', Unitary.quadraticForm v = 0) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) := by
  have hsq (u : originalHexadFixedCore h e X B) : u^2=1 := by
    let q : core z := ⟨u.val,originalHexadFixedCore_le h e X B u.property⟩
    have hv := (originalHexadFixedCore_native_mem h e X B B' he q).mp u.property
    have hz := hs _ hv
    change Unitary.quadraticForm (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))=0 at hz
    rw [coreNativeEquiv_quadratic] at hz
    have hq := (coreQuadraticForm_mk_eq_zero q).mp hz
    exact Subtype.ext (congrArg (fun x : core z => x.val) hq)
  have hi (u : originalHexadFixedCore h e X B) : u⁻¹=u :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq u)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  intro a b
  rw [←hi (a*b),mul_inv_rev,hi,hi]

/-- Cardinality transfer counts the original central line exactly once. -/
theorem originalHexadFixedCore_card_of_native (B B' : Finset (Fin 22))
    (he : (originalPlaneHexad e B).map (coreNativeProjection h e X) = nativeHexadStabilizer B')
    (hc : Nat.card (nativeHexadFixedSpace B')=64) :
    Nat.card (originalHexadFixedCore h e X B)=128 := by
  let U := (nativeHexadFixedSpace B').toAddSubgroup.toSubgroup
  let f := corePointProjection h e X
  let P := U.comap f
  have hm : P.map f = U := map_comap_eq_self_of_surjective (corePointProjection_surjective h e X) U
  have hk : f.ker ≤ P := ker_le_comap _ _
  have hU : Nat.card U=64 := by
    let eqv : U ≃ nativeHexadFixedSpace B' := {
      toFun x := ⟨x.val.toAdd,x.property⟩
      invFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_congr eqv).trans hc
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map P f
  rw [inf_eq_right.mpr hk,hm,hU,corePointProjection_ker,
    IsExtraspecial.center_order_p 2 (core z)] at hh
  rw [originalHexadFixedCore_native_preimage h e X B B' he,
    card_map_of_injective (core z).subtype_injective,←hh]

private theorem design_smul_block_mem (b : m22DesignAut) (B : Finset (Fin 22))
    (hB : B ∈ m22Blocks) : b • B ∈ m22Blocks := by
  have hb := b.property
  change b.val ∈ m22WittDesign.aut at hb
  rw [SteinerSystem.mem_aut_iff] at hb
  have hB' : B ∈ (m22WittDesign.blocks : Set (Finset (Fin 22))) := by
    simpa [m22WittDesign] using hB
  have hi := Set.smul_mem_smul_set (a := b.val) hB'
  rw [hb] at hi
  simpa [m22WittDesign, Subgroup.smul_def] using hi

/-- The native calculation at actual hexads discharges both source E₁ premises. -/
theorem originalHexadFixedCore_data_of_native
    (hnative : ∀ B ∈ m22Blocks, Nat.card (nativeHexadFixedSpace B)=64 ∧
      ∀ v ∈ nativeHexadFixedSpace B, Unitary.quadraticForm v=0)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) ∧
      Nat.card (originalHexadFixedCore h e X B)=128 := by
  obtain ⟨b,hb⟩ := originalPlaneHexad_native_image h e X
  obtain ⟨hc,hs⟩ := hnative (b • B) (design_smul_block_mem b B hB)
  exact ⟨originalHexadFixedCore_elementary_of_native h e X B (b • B) (hb B) hs,
    originalHexadFixedCore_card_of_native h e X B (b • B) (hb B) hc⟩

omit [IsExtraspecial 2 (core z)] in
/-- Apply the native fixed-space facts to the same source product E, retaining
its original normalizer and its intersection with Q. -/
theorem originalHexadElementary_data_of_native
    (hnative : ∀ B ∈ m22Blocks, Nat.card (nativeHexadFixedSpace B)=64 ∧
      ∀ v ∈ nativeHexadFixedSpace B, Unitary.quadraticForm v=0)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) ∧
    Nat.card (originalHexadFixedCore h e X B)=128 ∧
    IsElementaryAbelian 2 (originalHexadElementary h e X B) ∧
    Nat.card (originalHexadElementary h e X B)=2048 ∧
    originalPlaneHexad e B ≤ normalizer (originalHexadElementary h e X B : Set (centralizer z)) ∧
    originalHexadElementary h e X B ⊓ core z = originalHexadFixedCore h e X B := by
  let := h.extraspecial
  obtain ⟨hE1,hc⟩ := originalHexadFixedCore_data_of_native h e X hnative hB
  let := hE1
  exact ⟨hE1,hc,originalHexadElementary_elementary h e X hB,
    originalHexadElementary_card h e X hB hc,
    originalHexadElementary_normalized h e X hc,originalHexadElementary_inf_core h e X hc⟩


omit [IsExtraspecial 2 (core z)] in
/-- The standard native hexad calculation suffices for every original E. -/
theorem originalHexadElementary_data_of_standard
    (hc : Nat.card (nativeHexadFixedSpace m22Hexad123)=64)
    (hs : ∀ v ∈ nativeHexadFixedSpace m22Hexad123, Unitary.quadraticForm v=0)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) ∧
    Nat.card (originalHexadFixedCore h e X B)=128 ∧
    IsElementaryAbelian 2 (originalHexadElementary h e X B) ∧
    Nat.card (originalHexadElementary h e X B)=2048 ∧
    originalPlaneHexad e B ≤ normalizer (originalHexadElementary h e X B : Set (centralizer z)) ∧
    originalHexadElementary h e X B ⊓ core z = originalHexadFixedCore h e X B :=
  originalHexadElementary_data_of_native h e X
    (fun _ hB => nativeHexadFixedSpace_data_of_standard hc hs hB) hB

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
