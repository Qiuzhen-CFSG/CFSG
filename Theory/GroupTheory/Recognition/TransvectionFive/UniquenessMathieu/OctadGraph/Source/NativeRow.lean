module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowGeometry
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry

/-!
# The source row normalizer and a native octad stabilizer

The native octad kernel acts regularly on the complementary sixteen points.
Their point stabilizers therefore complement the actual intrinsic two-core.
Its existing cocode coordinates intertwine native conjugation with the full
GL₄(2) action. Reconstructing the source and native split extensions over
this same natural module gives an actual isomorphism from N_G(U₁) to the
stabilizer of any native octad. It has the prescribed kernel coordinates,
and those coordinates force agreement of the literal quotient actions.

This supplies the vertex-group isomorphism used in Aschbacher, *Sporadic
Groups* (1994), 41.4, p.222, with the native geometry of §§19–20, pp.96–99.
It does not yet assert that the map carries the marked line and plane flags
to the chosen native flags, or agrees there with a local-plane isomorphism.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace NativeRow
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction

/-- A point off the octad gives an actual complement to its intrinsic core. -/
theorem core_complement (O : Octad) (x : Fin 24) (hx : x ∉ O.val) :
    (Core O).IsComplement' (MulAction.stabilizer (Stabilizer O) x) := by
  apply Subgroup.isComplement'_stabilizer
  · intro a ha
    by_contra hne
    have hne' : ((a : Stabilizer O) : M24) ≠ 1 := by
      intro h
      exact hne (Subtype.ext (Subtype.ext h))
    exact hx ((MathieuCode.octad_kernel_fixed_point_iff O a
      (by simpa only [corePointwiseEquiv_coe] using (corePointwiseEquiv O a).property) hne' x).mp ha)
  · intro g
    have hgx : (g : M24) • x ∉ O.val := by
      intro h
      apply hx
      have hh := (MulAction.mem_stabilizer_finset'.mp (g⁻¹).property) h
      simpa only [Subgroup.coe_inv, inv_smul_smul] using hh
    obtain ⟨a, ha⟩ := MathieuCode.octad_kernel_transitive O ((g : M24) • x) x hgx hx
    exact ⟨(corePointwiseEquiv O).symm a, by
      change (((corePointwiseEquiv O).symm a : Stabilizer O) : M24) • ((g : M24) • x) = x
      rw [← corePointwiseEquiv_coe, MulEquiv.apply_symm_apply]
      exact ha⟩

/-- Splitting of the native octad stabilizer by its literal core, obtained
from the regular action on the sixteen complementary points. -/
theorem core_splits (O : Octad) :
    ∃ K : Subgroup (Stabilizer O), (Core O).IsComplement' K := by
  classical
  have hx : ∃ x : Fin 24, x ∉ O.val := by
    by_contra h
    push Not at h
    have he : O.val = Finset.univ := Finset.eq_univ_of_forall h
    have hc := m24Blocks_card O.val O.property
    rw [he] at hc
    norm_num at hc
  obtain ⟨x, hx⟩ := hx
  exact ⟨_, core_complement O x hx⟩

/-- The common natural action in both source and native split coordinates. -/
@[expose] def natural : (Space ≃ₗ[ZMod 2] Space) →* MulAut (Multiplicative Space) where
  toFun f := f.toAddEquiv.toMultiplicative
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The native extension is the natural affine four-space group, with its
actual intrinsic kernel coordinates prescribed. -/
theorem exists_affine_equiv (O : Octad) :
    ∃ e : Stabilizer O ≃* Multiplicative Space ⋊[natural] (Space ≃ₗ[ZMod 2] Space),
      ∀ a : Core O, e a = SemidirectProduct.inl (coreCoordinates O a) := by
  obtain ⟨K, hK⟩ := core_splits O
  obtain ⟨e, he, _⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    (Core O) K hK (quotientLinearEquiv O) (coreCoordinates O) natural (by
      intro g a
      apply Multiplicative.toAdd.injective
      have h := coreCoordinates_conjugation O g a
      rw [naturalAction_quotientEquiv] at h
      change (coreCoordinates O (MulAut.conjNormal g a)).toAdd =
        quotientLinearEquiv O (QuotientGroup.mk g) (coreCoordinates O a).toAdd
      rw [quotientLinearEquiv_mk]
      have he : MulAut.conjNormal g a = coreConjugate O g a := by
        apply Subtype.ext
        exact (coreConjugate_coe O g a).symm
      rw [he]
      exact h)
  exact ⟨e, he⟩

end NativeRow
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

include D in
/-- An actual source-row/native-octad isomorphism, with the original row
coordinates matched to the native kernel coordinates. -/
theorem exists_native_row_equiv (O : Octad) :
    ∃ e : rowNormalizer F ≃* Stabilizer O,
      ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        ((coreCoordinates O).symm (rowCoordinates F a) : Stabilizer O) := by
  let A := F.row.subgroupOf (rowNormalizer F)
  let c : A ≃* Multiplicative Space :=
    (subgroupOfEquivOfLe F.row.le_normalizer).trans (rowCoordinates F)
  obtain ⟨K, hK⟩ := LocalData.row_splits F
  obtain ⟨f, hf, _⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    A K hK (LocalData.rowEquiv F D) c NativeRow.natural (by
      intro g a
      apply Multiplicative.toAdd.injective
      exact (LocalData.rowEquiv_action F D g ((subgroupOfEquivOfLe F.row.le_normalizer) a)).symm)
  obtain ⟨f', hf'⟩ := NativeRow.exists_affine_equiv O
  refine ⟨f.trans f'.symm, fun a => ?_⟩
  apply f'.injective
  change f' (f'.symm (f (inclusion F.row.le_normalizer a))) = _
  rw [f'.apply_symm_apply]
  have h := hf ((subgroupOfEquivOfLe F.row.le_normalizer).symm a)
  exact h.trans ((hf' ((coreCoordinates O).symm (rowCoordinates F a))).trans
    (congrArg SemidirectProduct.inl ((coreCoordinates O).apply_symm_apply _))).symm

omit [Finite G] in
/-- The prescribed kernel map forces the original quotient actions to agree.
Thus the native comparison is compatible with conjugation, not just order. -/
theorem native_row_equiv_action (O : Octad)
    (e : rowNormalizer F ≃* Stabilizer O)
    (he : ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
      ((coreCoordinates O).symm (rowCoordinates F a) : Stabilizer O))
    (n : rowNormalizer F) : linearAction O (e n) = rowAction F D n := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, ha⟩ := (rowCoordinates F).surjective (Multiplicative.ofAdd v)
  let b := (coreCoordinates O).symm (rowCoordinates F a)
  have hconj := congrArg e (show inclusion F.row.le_normalizer
    (F.row.normalizerMonoidHom n a) =
      n * inclusion F.row.le_normalizer a * n⁻¹ from rfl)
  rw [he, map_mul, map_mul, map_inv, he] at hconj
  have hb : coreConjugate O (e n) b =
      (coreCoordinates O).symm (rowCoordinates F (F.row.normalizerMonoidHom n a)) := by
    apply Subtype.ext
    rw [coreConjugate_coe]
    exact hconj.symm
  have hc := coreCoordinates_conjugation O (e n) b
  rw [naturalAction_quotientEquiv, hb, MulEquiv.apply_symm_apply] at hc
  have hba : coreCoordinates O b = rowCoordinates F a := (coreCoordinates O).apply_symm_apply _
  rw [hba, ha] at hc
  have hs := rowAction_coordinates F D n a
  rw [ha] at hs
  exact hc.symm.trans hs.symm

/-- Both the native intrinsic kernel and the actual quotient action are
matched by the same source-row isomorphism. -/
theorem exists_native_row_equiv_action (O : Octad) :
    ∃ e : rowNormalizer F ≃* Stabilizer O,
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        ((coreCoordinates O).symm (rowCoordinates F a) : Stabilizer O)) ∧
      ∀ n, linearAction O (e n) = rowAction F D n := by
  obtain ⟨e, he⟩ := exists_native_row_equiv F D O
  exact ⟨e, he, native_row_equiv_action F D O e he⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
