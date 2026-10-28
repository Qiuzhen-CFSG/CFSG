module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Octad

/-!
# Radical saturation of an octad translation image

Every nonidentity octad translation fixes exactly that octad. Consequently
the full normalizer of any nontrivial subgroup of the translation kernel
preserves the octad. Radical saturation then forces the entire kernel into
a radical image. The literal native Mathieu projection lifts this equality
to the actual octad-preimage radical and its full intrinsic A₈ quotient.

This removes every proper nontrivial subgroup of an octad kernel from the
remaining Mathieu-image problem. Placement in such a kernel is a separate
geometric assertion; no Sylow-normality hypothesis is used here.
Source: An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124,
and the native octad action in `M24ChapterHStabilizers.OctadAction`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

/-- The common fixed octad controls the entire normalizer, even for a
proper nontrivial subgroup of its pointwise kernel. -/
theorem normalizer_le_octad_of_le_kernel (A : Subgroup M24) (hne : A ≠ ⊥)
    (O : Octad) (hA : A ≤ octadPointwiseKernel O) :
    normalizer (A : Set M24) ≤ octadStabilizer O := by
  obtain ⟨z,hz,hz1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  intro g hg
  have hz' : g * z * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg z).mp hz
  have hz1' : g * z * g⁻¹ ≠ 1 := by
    change (MulAut.conj g) z ≠ 1
    intro he
    exact hz1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp he)
  change g • O.val = O.val
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_smul_finset.mp hj
    apply (octad_kernel_fixed_point_iff O _ (hA hz') hz1' _).mp
    rw [mul_smul, mul_smul, inv_smul_smul,
      (octad_kernel_fixed_point_iff O z (hA hz) hz1 i).mpr hi]
  · simp

/-- A nontrivial radical subgroup of an octad kernel is the whole kernel. -/
theorem radical_eq_octad_kernel (A : Subgroup M24) (hA : A.IsPRadical 2)
    (O : Octad) (hle : A ≤ octadPointwiseKernel O) : A = octadPointwiseKernel O := by
  have hn := normalizer_le_octad_of_le_kernel A hA.1 O hle
  have hc : (octadStabilizer O).pCoreIn 2 ≤ A :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le A _ hA.isPGroup
      (isPGroup_pCoreIn 2 _) hA.2.le
      (hn.trans ((octadStabilizer O).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (octadStabilizer O)))))
  change (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype ≤ A at hc
  rw [octad_core_map_eq_pointwise] at hc
  exact le_antisymm hle hc

/-- Apply saturation to the literal native image, retaining the full ambient
radical rather than an abstract subgroup of the same order. -/
theorem radical_eq_octadRadical_of_image_le (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1)
    (hne : (P.subgroupOf max1).map projection ≠ ⊥)
    (O : Octad) (hle : (P.subgroupOf max1).map projection ≤ octadPointwiseKernel O) :
    P = octadRadical O := by
  have he := radical_eq_octad_kernel _ ⟨hne,radical_image_core P hP hN⟩ O hle
  rw [radical_eq_preimage P hP hN, he]

/-- The literal full-core normalizer quotient for every such native image. -/
def radicalOctadImageQuotientEquiv (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1)
    (hne : (P.subgroupOf max1).map projection ≠ ⊥)
    (O : Octad) (hle : (P.subgroupOf max1).map projection ≤ octadPointwiseKernel O) :
    (normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8) := by
  have he := radical_eq_octadRadical_of_image_le P hP hN hne O hle
  subst P
  exact octadRadicalQuotientEquiv O

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
