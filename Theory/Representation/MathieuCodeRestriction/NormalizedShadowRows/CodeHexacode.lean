module
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags

/-!
# The translation moved space of the M24 code

In raw sextet coordinates the hexacode translations move precisely the
11-dimensional even-column Golay subcode. A small kernel-checked difference
certificate proves generation; the affine encoder proves the reverse
containment. Transport through the same sextet marking and the constant-line
quotient gives the actual 10-dimensional moved hyperplane in the native code.

Source: Aschbacher--Smith H.16.1(3) and 8.2.8(5), printed pp.402,718,
refs/quasithin.pdf. The sextet coordinates and encoder are the licensed ATLAS
port by Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open scoped BigOperators
open Atlas.Codes
namespace MathieuCode.NormalizedShadowRows.CodeHexacode
noncomputable section

private def difference (i : Fin 6) (j : Fin 12) : BinaryWord :=
  coordinatePermutation (affinePermutation (hexGenerators i) 1) (golayGenerators j) -
    golayGenerators j

private def translationIndex : Fin 11 → Fin 6 := ![0,0,0,0,1,1,2,2,3,4,5]
private def wordIndex : Fin 11 → Fin 12 := ![1,2,3,11,3,11,4,11,11,11,11]
private def certificate : Fin 11 → Finset (Fin 11) :=
  ![{0,1,2,3},{1,4,5},{0,6,7},{2,4,8},{2,6,9},{0,6,10},{2},{0},{0,4},{1},{1,6}]

private theorem certificate_checked : ∀ i : Fin 11,
    (∑ k ∈ certificate i, difference (translationIndex k) (wordIndex k)) =
      golayGenerators i.castSucc := by
  decide +kernel

/-- The raw translation commutator span, before quotienting by constants. -/
def rawMoved : Submodule Bit BinaryWord :=
  Submodule.span Bit {v | ∃ t : hexacode, ∃ w ∈ Atlas.Codes.golay,
    v = coordinatePermutation (sextetTranslation (Multiplicative.ofAdd t)).val.val w - w}

private lemma difference_mem (i : Fin 6) (j : Fin 12) : difference i j ∈ rawMoved := by
  have ht : hexGenerators i ∈ hexacode := by rw [← hexBasis_coe]; exact (hexBasis i).property
  have hw : golayGenerators j ∈ Atlas.Codes.golay := by rw [← golayBasis_coe]; exact (golayBasis j).property
  exact Submodule.subset_span ⟨⟨hexGenerators i,ht⟩,golayGenerators j,hw,rfl⟩

private lemma generator_mem (i : Fin 11) : golayGenerators i.castSucc ∈ rawMoved := by
  rw [← certificate_checked i]
  exact rawMoved.sum_mem fun k _ => difference_mem _ _

private lemma hex_mem (h : hexacode) : jWord h.val ∈ rawMoved := by
  have he := congrArg (fun x : hexacode => jWord x.val) (hexBasis.sum_repr h)
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,map_sum,map_smul] at he
  rw [← he]
  apply rawMoved.sum_mem
  intro i _
  apply rawMoved.smul_mem
  rw [hexBasis_coe]
  have hh : jWord (hexGenerators i) = golayGenerators (i.castLE (by decide)) := by
    revert i
    decide +kernel
  rw [hh]
  exact generator_mem ⟨i.val,by omega⟩

private lemma repetition_mem (r : P6) : rho r.val ∈ rawMoved := by
  have he := congrArg (fun x : P6 => rho x.val) ((parityBasis 5).sum_repr r)
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,map_sum,map_smul] at he
  rw [← he]
  apply rawMoved.sum_mem
  intro i _
  apply rawMoved.smul_mem
  rw [parityBasis_coe]
  have hh : rho (Pi.single 0 1 + Pi.single i.succ 1) =
      golayGenerators ⟨6+i.val,by omega⟩ := by
    revert i
    decide +kernel
  rw [hh]
  exact generator_mem ⟨6+i.val,by omega⟩

private lemma translation_parity (t : hexacode) (w : BinaryWord) (hw : w ∈ Atlas.Codes.golay)
    (i : HexIndex) :
    blockParity (coordinatePermutation (sextetTranslation (Multiplicative.ofAdd t)).val.val w) i =
      blockParity w i := by
  obtain ⟨⟨h,r,ε⟩,he⟩ := golayEquiv.surjective ⟨w,hw⟩
  have he' := (rowEncoder_golayEquiv h r ε).trans (congrArg Subtype.val he)
  change rowEncoder h.val (fun i => r.val (hexIndexEquiv i)) ε = w at he'
  rw [← he']
  change blockParity (coordinatePermutation (affinePermutation t.val 1)
    (rowEncoder h.val (fun i => r.val (hexIndexEquiv i)) ε)) i = _
  rw [affine_encoder_transform,rowEncoder_blockParity,rowEncoder_blockParity]

/-- The exact raw moved space is the eleven-dimensional even-column code. -/
theorem rawMoved_eq_C0 : rawMoved = C0 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨t,w,hw,rfl⟩
    apply (C0_even_blocks _).mpr
    refine ⟨Atlas.Codes.golay.sub_mem ((sextetTranslation (Multiplicative.ofAdd t)).val.property w |>.mp hw) hw, ?_⟩
    intro i
    apply (even_weight_iff _).mpr
    change (∑ k, (coordinatePermutation (sextetTranslation (Multiplicative.ofAdd t)).val.val w (i,k) - w (i,k))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (translation_parity t w hw i)
  · rintro w ⟨⟨h,r⟩,rfl⟩
    exact rawMoved.add_mem (hex_mem h) (repetition_mem r)


open Representation.BinaryOffender
open MathieuCode.SextetLayers MathieuCode.SextetLayers.CoordinateTransport
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

/-- The even-column subcode inside the raw Golay code. -/
def evenGolay : Submodule Bit Atlas.Codes.golay := C0.comap Atlas.Codes.golay.subtype

lemma C0_le_golay : C0 ≤ Atlas.Codes.golay := fun w hw => ((C0_even_blocks w).mp hw).1

lemma evenGolay_finrank : Module.finrank Bit evenGolay = 11 :=
  (Submodule.comapSubtypeEquivOfLe C0_le_golay).finrank_eq.trans C0_finrank

def rawGolayRepresentation : Representation Bit Atlas.Codes.SextetStabilizer Atlas.Codes.golay where
  toFun g := (atlasFullRepresentation g).restrict (fun w hw => (g.val.property w).mp hw)
  map_one' := by ext w; rfl
  map_mul' _ _ := by ext w; rfl

lemma rawGolay_moved :
    subspaceCommutator rawGolayRepresentation ⊤ sextetTranslation.range = evenGolay := by
  have hh := subspaceCommutator_map_embedding atlasFullRepresentation rawGolayRepresentation
    (MonoidHom.id _) Atlas.Codes.golay.subtype (fun _ _ => rfl) sextetTranslation.range ⊤
  rw [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at hh
  have he : subspaceCommutator atlasFullRepresentation Atlas.Codes.golay sextetTranslation.range = rawMoved := by
    change Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext v
    constructor
    · rintro ⟨g,⟨t,rfl⟩,w,hw,rfl⟩
      exact ⟨t.toAdd,w,hw,rfl⟩
    · rintro ⟨t,w,hw,rfl⟩
      exact ⟨_,⟨Multiplicative.ofAdd t,rfl⟩,w,hw,rfl⟩
  rw [he,rawMoved_eq_C0] at hh
  apply (Submodule.map_injective_of_injective Atlas.Codes.golay.subtype_injective)
  rw [← hh, evenGolay, Submodule.map_comap_subtype, inf_eq_right.mpr C0_le_golay]

/-- The same coordinate marking restricts to the full Golay codes. -/
def golayCoordinates (S : Sextet) : Atlas.Codes.golay ≃ₗ[Bit] MathieuCode.golay :=
  (nativeMarking S).wordEquiv.ofSubmodules _ _ (nativeMarking S).golay_map

lemma golayCoordinates_equivariant (S : Sextet) (g : Atlas.Codes.SextetStabilizer)
    (w : Atlas.Codes.golay) :
    golayCoordinates S (rawGolayRepresentation g w) =
      golayRepresentation (nativeStabilizerEquiv S g).val (golayCoordinates S w) := by
  apply Subtype.ext
  exact (nativeMarking S).wordEquiv_equivariant g _ (nativeStabilizer_coordinates S g) w.val

/-- The even-column hyperplane in the literal native code quotient. -/
def evenCode (S : Sextet) : Submodule Bit Code :=
  (evenGolay.map (golayCoordinates S).toLinearMap).map codeLine.mkQ

lemma sextetCore_moved (S : Sextet) :
    subspaceCommutator codeRepresentation ⊤ (CodeFlags.sextetCore S) = evenCode S := by
  let f : Multiplicative hexacode →* M24 :=
    (sextetStabilizer S).subtype.comp (nativeTranslation S)
  have hf : f.range = CodeFlags.sextetCore S := by
    dsimp only [f]
    rw [MonoidHom.range_comp, CodeFlags.nativeTranslation_range_eq_core]
    rfl
  have hraw := subspaceCommutator_comp_map rawGolayRepresentation sextetTranslation ⊤ ⊤
  rw [← MonoidHom.range_eq_map, rawGolay_moved] at hraw
  have heq := subspaceCommutator_map_embedding (codeRepresentation.comp f)
    (rawGolayRepresentation.comp sextetTranslation) (MonoidHom.id _)
    (codeLine.mkQ.comp (golayCoordinates S).toLinearMap)
    (fun t w => by
      rw [MonoidHom.id_apply]
      change codeRepresentation (f t) (codeLine.mkQ (golayCoordinates S w)) = _
      rw [codeRepresentation_mk]
      change codeLine.mkQ (golayRepresentation (nativeStabilizerEquiv S (sextetTranslation t)).val
        (golayCoordinates S w)) = codeLine.mkQ (golayCoordinates S (rawGolayRepresentation (sextetTranslation t) w))
      rw [golayCoordinates_equivariant]) ⊤ ⊤
  have hsur : Function.Surjective (codeLine.mkQ.comp (golayCoordinates S).toLinearMap) :=
    codeLine.mkQ_surjective.comp (golayCoordinates S).surjective
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsur, Subgroup.map_id, hraw,
    subspaceCommutator_comp_map, ← MonoidHom.range_eq_map, hf] at heq
  exact heq.trans (Submodule.map_comp _ _ _ )

lemma codeLine_le_even (S : Sextet) :
    codeLine ≤ evenGolay.map (golayCoordinates S).toLinearMap := by
  intro w hw
  refine ⟨(golayCoordinates S).symm w, ?_, (golayCoordinates S).apply_symm_apply w⟩
  change ((golayCoordinates S).symm w).val ∈ C0
  apply (C0_even_blocks _).mpr
  refine ⟨((golayCoordinates S).symm w).property, ?_⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  intro i
  apply (even_weight_iff _).mpr
  change (∑ k, w.val ((nativeMarking S).pointEquiv (i,k))) = 0
  change _ = w.val at hc
  simp only [← hc]
  simp only [Pi.smul_apply, BinaryPermutation.allOne, smul_eq_mul, mul_one]
  change (∑ _k : Fin 4, c) = 0
  simp only [Finset.sum_const, Finset.card_univ]
  fin_cases c <;> decide +kernel

lemma evenCode_finrank (S : Sextet) : Module.finrank Bit (evenCode S) = 10 := by
  let W := evenGolay.map (golayCoordinates S).toLinearMap
  let q := codeLine.mkQ.domRestrict W
  have hr : LinearMap.range q = evenCode S := by
    change LinearMap.range (codeLine.mkQ.comp W.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hk : LinearMap.ker q = codeLine.comap W.subtype := by
    ext w
    exact Submodule.Quotient.mk_eq_zero codeLine
  have hd := q.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe (codeLine_le_even S)).finrank_eq,
    finrank_codeLine] at hd
  have hW : Module.finrank Bit W = 11 :=
    ((golayCoordinates S).finrank_map_eq evenGolay).trans evenGolay_finrank
  rw [hW] at hd
  change Module.finrank Bit (evenCode S) + 1 = 11 at hd
  omega

lemma sextetCore_moved_finrank (S : Sextet) :
    Module.finrank Bit (subspaceCommutator codeRepresentation ⊤ (CodeFlags.sextetCore S)) = 10 := by
  rw [sextetCore_moved, evenCode_finrank]

end
end MathieuCode.NormalizedShadowRows.CodeHexacode
