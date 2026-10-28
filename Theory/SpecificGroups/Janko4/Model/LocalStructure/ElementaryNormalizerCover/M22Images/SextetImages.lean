module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetKernel

/-!
# The five octad cases and thirty remaining sextet four-groups

The literal native E16 has five classes of nonidentity translations with
a common fixed octad. If a subgroup has elements from different classes,
their products give one of the thirty displayed four-groups. Otherwise its
whole image fixes one of the five certified native octads pointwise.

This is the quotient-image split in Kleidman--Wilson (1988), Proposition
2.2.2(iii), pp.490--491. The following lift uses the actual pointwise octad
kernels and the non-octad pairs checked in `SextetKernel`.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetImages
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open M23Geometry FusionCertificate ElementarySylow SextetKernel
private def lineNumber : Fin 16 → Fin 5 := ![0,0,0,0,1,2,3,4,1,4,2,3,1,3,4,2]
private def octadIndex : Fin 5 → Fin 759 := ![213,393,641,585,500]
def octad (k : Fin 5) : M24LocalGeometry.Octad := ⟨m24BlockAt (octadIndex k), by
  rw [m24Blocks]; exact Finset.mem_image.mpr ⟨octadIndex k,Finset.mem_univ _,rfl⟩⟩
private theorem line_fixed : ∀ (i : Fin 16) (x : Fin 24),
  x ∈ (octad (lineNumber i)).val → CommonFour.extendPoint (pointTable (candidateIndex 0 i)) x = x := by decide +kernel
private theorem pair_or_line : ∀ (i j : Fin 16), i ≠ 0 →
  (j = 0 ∨ lineNumber j = lineNumber i) ∨
  ∃ k : Fin 30,
    (nonOctadPair k 0 = i ∨ nonOctadPair k 0 = j ∨ nonOctadPair k 0 = i ^^^ j) ∧
    (nonOctadPair k 1 = i ∨ nonOctadPair k 1 = j ∨ nonOctadPair k 1 = i ^^^ j) := by decide +kernel

private theorem imageElement_mul (i j : Fin 16) :
    imageElement i * imageElement j = imageElement (i ^^^ j) := by
  rw [imageElement,imageElement,← map_mul]
  congr 1
  exact Subtype.ext (product_correct 0 i j)

private theorem imageElement_zero : imageElement 0 = 1 := by
  change pointEmbedding (sylowElement 0) = 1
  rw [show sylowElement 0 = 1 from Subtype.ext initial,map_one]

/-- Every subgroup of the sextet E16 either fixes a literal octad pointwise,
or contains one of the thirty non-octad four-groups. -/
theorem subgroup_octad_or_pair (A : Subgroup M24) (hA : A ≤ imageGroup) :
    (∃ k : Fin 5, A ≤ octadPointwiseKernel (octad k)) ∨
    ∃ k : Fin 30, ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ A := by
  classical
  by_cases hp : ∃ k : Fin 30, ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ A
  · exact Or.inr hp
  left
  by_cases hnon : ∃ i : Fin 16, i ≠ 0 ∧ imageElement i ∈ A
  · obtain ⟨i,hi,hiA⟩ := hnon
    refine ⟨lineNumber i,?_⟩
    intro a ha
    obtain ⟨p,⟨j,hj⟩,hpa⟩ := hA ha
    have he : imageElement j = a := by
      rw [imageElement,show sylowElement (candidateIndex 0 j) = p from Subtype.ext hj]
      exact hpa
    have hjA : imageElement j ∈ A := he.symm ▸ ha
    have hline : j = 0 ∨ lineNumber j = lineNumber i := by
      rcases pair_or_line i j hi with h | ⟨k,hk0,hk1⟩
      · exact h
      · exfalso
        apply hp
        have hm : imageElement (i ^^^ j) ∈ A := imageElement_mul i j ▸ A.mul_mem hiA hjA
        have mem (r : Fin 16) (hr : r = i ∨ r = j ∨ r = i ^^^ j) : imageElement r ∈ A := by
          rcases hr with rfl | rfl | rfl
          · exact hiA
          · exact hjA
          · exact hm
        exact ⟨k,fun d => by fin_cases d; exact mem _ hk0; exact mem _ hk1⟩
    rw [← he]
    rcases hline with rfl | hline
    · rw [imageElement_zero]; exact one_mem _
    apply (mem_octadPointwiseKernel _ _).mpr
    intro x hx
    change (pointEmbedding (sylowElement (candidateIndex 0 j))).val x = x
    rw [CommonFour.pointEmbedding_apply_all]
    exact line_fixed j x (hline.symm ▸ hx)
  · refine ⟨0,?_⟩
    intro a ha
    obtain ⟨p,⟨i,hi⟩,hpa⟩ := hA ha
    have he : imageElement i = a := by
      rw [imageElement,show sylowElement (candidateIndex 0 i) = p from Subtype.ext hi]
      exact hpa
    have hi0 : i = 0 := by
      by_contra hn
      exact hnon ⟨i,hn,he.symm ▸ ha⟩
    rw [← he,hi0,imageElement_zero]
    exact one_mem _

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetImages
