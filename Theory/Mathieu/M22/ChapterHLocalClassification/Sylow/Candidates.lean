module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Marking

/-!
# The two source-marked elementary candidates in M22

The corrected Sylow conjugator carries the native sextet translation group
onto the literal mapped intrinsic sextet core. Its checked 64-element list
therefore counts the restrictions to the pointwise and setwise pair groups:
their orders are 16 and 32. A translation fixing the deleted pair but moving
point 7 distinguishes the inner candidate from the intrinsic hexad E16.
The actual embeddings and conjugation maps are retained throughout.

Source: Aschbacher--Smith H.14.3(1), printed pp.396--397. The classification
of arbitrary elementary subgroups is supplied separately.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow
open SylowNormalizer.OrderEnumeration

private def correction : M24 := transport * M24ChapterHStabilizers.ElementaryFusion.transport⁻¹

private theorem correction_sextet :
    m22SourceSextet.parts = correction • standardSextet.parts := by
  change m22SourceSextet.parts =
    (transportPerm * M24ChapterHStabilizers.ElementaryFusion.transportPerm⁻¹) • standardSextet.parts
  decide +kernel

/-- The same corrected conjugator sends the native translation candidate onto
exactly the mapped intrinsic source sextet core. -/
theorem sourceCore_eq_candidate : Sextet.sourceCore =
    (EvenCandidates.elementary 1).map (MulAut.conj transport).toMonoidHom := by
  let e : sextetStabilizer standardSextet ≃* sextetStabilizer m22SourceSextet :=
    MulAction.stabilizerEquivStabilizer correction_sextet
  have he : (sextetStabilizer m22SourceSextet).subtype.comp e.toMonoidHom =
      (MulAut.conj correction).toMonoidHom.comp (sextetStabilizer standardSextet).subtype := by
    apply MonoidHom.ext
    intro g
    exact MulAction.stabilizerEquivStabilizer_apply correction_sextet g
  have hc : Sextet.sourceCore = SextetCore.core.map (MulAut.conj correction).toMonoidHom := by
    rw [Sextet.sourceCore, ← pCore_map_iso 2 e, Subgroup.map_map, he, ← Subgroup.map_map]
    rfl
  rw [hc, ← M24ChapterHStabilizers.ElementaryFusion.sextetCandidate_eq_core,
    M24ChapterHStabilizers.ElementaryFusion.markedCandidate, Subgroup.map_map]
  congr 1
  ext x
  simp [correction, MulAut.conj_apply, mul_assoc]

open EvenCatalogue.NormalizerOvergroupsProof in
def coreIndex (j : Fin 64) : Fin 1024 := elementIndex (rowCode 21 j)

theorem coreIndex_injective : Function.Injective coreIndex := by decide +kernel

theorem mem_sourceCore (g : M24) : g ∈ Sextet.sourceCore ↔
    ∃ j : Fin 64, row (coreIndex j) = g := by
  rw [sourceCore_eq_candidate]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← EvenCatalogue.NormalizerOvergroupsProof.last_ambient 1] at ha
    obtain ⟨j, rfl⟩ := (EvenCatalogue.NormalizerOvergroupsProof.mem_ambient_iff 21 a).mp ha
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨_, ?_, rfl⟩
    rw [← EvenCatalogue.NormalizerOvergroupsProof.last_ambient 1]
    exact EvenCatalogue.NormalizerOvergroupsProof.rowElement_mem 21 j

abbrev InnerCoreIndex := {j : Fin 64 // point (coreIndex j) 0 = 0 ∧ point (coreIndex j) 9 = 9}
abbrev OuterCoreIndex := {j : Fin 64 // point (coreIndex j) 0 ∈ m22Pair ∧ point (coreIndex j) 9 ∈ m22Pair}

private theorem innerCoreIndex_card : Fintype.card InnerCoreIndex = 16 := by decide +kernel
private theorem outerCoreIndex_card : Fintype.card OuterCoreIndex = 32 := by decide +kernel

private def innerCoreElement (i : InnerCoreIndex) : Sextet.innerTranslations := by
  have hi := (row_inner_iff (coreIndex i.val)).mpr i.property
  exact ⟨hi.choose, by
    change m22Embedding hi.choose ∈ Sextet.sourceCore
    rw [hi.choose_spec]
    exact (mem_sourceCore _).mpr ⟨i.val, rfl⟩⟩

private theorem innerCoreElement_embedding (i : InnerCoreIndex) :
    m22Embedding (innerCoreElement i).val = row (coreIndex i.val) :=
  ((row_inner_iff (coreIndex i.val)).mpr i.property).choose_spec

private def outerCoreElement (i : OuterCoreIndex) : Sextet.outerTranslations :=
  ⟨⟨row (coreIndex i.val), (row_outer_iff (coreIndex i.val)).mpr i.property⟩,
    (mem_sourceCore _).mpr ⟨i.val, rfl⟩⟩

private theorem innerCoreElement_bijective : Function.Bijective innerCoreElement := by
  constructor
  · intro i j h
    apply Subtype.ext
    apply coreIndex_injective
    apply row_injective
    simpa only [innerCoreElement_embedding] using
      congrArg (fun g : Sextet.innerTranslations => m22Embedding g.val) h
  · intro g
    obtain ⟨j, hj⟩ := (mem_sourceCore (m22Embedding g.val)).mp g.property
    have hp := (row_inner_iff (coreIndex j)).mp (hj.symm ▸ (show m22Embedding g.val ∈
      m22Embedding.range from ⟨g.val, rfl⟩))
    refine ⟨⟨j, hp⟩, Subtype.ext (m22Embedding_injective ?_)⟩
    exact (innerCoreElement_embedding _).trans hj

private theorem outerCoreElement_bijective : Function.Bijective outerCoreElement := by
  constructor
  · intro i j h
    exact Subtype.ext (coreIndex_injective (row_injective
      (congrArg (fun g : Sextet.outerTranslations => g.val.val) h)))
  · intro g
    obtain ⟨j, hj⟩ := (mem_sourceCore g.val.val).mp g.property
    exact ⟨⟨j, (row_outer_iff (coreIndex j)).mp (hj.symm ▸ g.val.property)⟩,
      Subtype.ext (Subtype.ext hj)⟩

theorem innerTranslations_card : Nat.card Sextet.innerTranslations = 16 := by
  rw [← Nat.card_congr (Equiv.ofBijective innerCoreElement innerCoreElement_bijective),
    Nat.card_eq_fintype_card, innerCoreIndex_card]

theorem outerTranslations_card : Nat.card Sextet.outerTranslations = 32 := by
  rw [← Nat.card_congr (Equiv.ofBijective outerCoreElement outerCoreElement_bijective),
    Nat.card_eq_fintype_card, outerCoreIndex_card]

/-- A source translation fixes the deleted pair but moves the remaining hexad. -/
theorem inner_candidates_distinct : m22InnerHexadKernel m22SourceOctad ≠
    Sextet.innerTranslations := by
  have hw : ∃ j : Fin 64, point (coreIndex j) 0 = 0 ∧ point (coreIndex j) 9 = 9 ∧
      point (coreIndex j) 7 ≠ 7 := by decide +kernel
  obtain ⟨j, h0, h9, h2⟩ := hw
  let v := innerCoreElement ⟨j, h0, h9⟩
  intro he
  have hv : v.val ∈ m22InnerHexadKernel m22SourceOctad := he.symm ▸ v.property
  have hm := Subgroup.mem_map_of_mem m22Embedding hv
  rw [Hexad.inner_kernel_image] at hm
  have hf := (mem_octadPointwiseKernel m22SourceOctad (m22Embedding v.val)).mp hm
    7 (by decide +kernel)
  rw [innerCoreElement_embedding] at hf
  exact h2 ((row_apply _ _).symm.trans hf)

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
