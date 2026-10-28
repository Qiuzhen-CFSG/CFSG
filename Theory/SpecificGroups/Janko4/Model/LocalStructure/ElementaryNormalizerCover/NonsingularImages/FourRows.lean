module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.SylowRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Positioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.FigureA

/-!
# Four native containers for the nonsingular quotient image

Native word certificates fuse the six Sylow containers: three map to the
existing whole (b), (c), and (d) source images, while the other two lie in a
conjugate of the literal (a) container. Every conjugator centralizes the original
pair permutation and fixes the seed pair. Sylow conjugacy therefore gives
four-container placement inside the literal marked quotient, with no new
classification or positioning premise.

Containment is asserted here; the source refinement to equality with (b),
(c), (d) or a primed row still needs its proper-subgroup analysis. `SourceRows`
uses the original seed-centralizer quotient to lift the actual conjugators.
Source: Kleidman--Wilson (1988), Figure 2 and Lemma 2.3.1, pp.490,492.
-/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Subgroup Theory.GroupTheory Cardinality.QuotientCount.Image Cardinality.KernelCount
open ElementaryEightGeometry
open scoped Pointwise

/-- The literal Figure 2(a) container, including the Figure 1 pair permutation. -/
@[expose] def boxImage : Subgroup StarGroup := FigureA.wholeImage

/-- The four literal whole-image containers. -/
@[expose] def sourceRow : Fin 4 → Subgroup StarGroup :=
  ![boxImage, pairRowImage 0, NonsingularC.wholeImage, pairRowImage 1]

private def sourceGenerator (k : Fin 4) (j : Fin 5) : StarGroup :=
  ![FigureA.wholeGenerator,
    fun j => pairRowGenerator 0 ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩,
    fun j => NonsingularC.wholeGenerator ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩,
    fun j => pairRowGenerator 1 ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩] k j

private theorem sourceGenerator_mem (k : Fin 4) (j : Fin 5) :
    sourceGenerator k j ∈ sourceRow k := by
  fin_cases k
  · exact FigureA.wholeGenerator_mem j
  · exact pairRowGenerator_mem 0 _
  · exact subset_closure ⟨⟨j.val % 4, Nat.mod_lt _ (by decide)⟩,rfl⟩
  · exact pairRowGenerator_mem 1 _

private def sourcePoint : Fin 4 → Fin 5 → Fin 24 → Fin 24 :=
![![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 2, 3, 5, 4, 13, 17, 14, 18, 22, 11, 12, 6, 8, 16, 15, 7, 9, 19, 20, 23, 10, 21], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6]], ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23]], ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 18, 10, 7, 16, 6, 4, 17, 19, 3, 11, 12, 13, 15, 14, 5, 8, 2, 9, 22, 21, 20, 23], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23]], ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 20, 19, 4, 5, 23, 16, 8, 18, 22, 11, 12, 21, 14, 17, 7, 15, 9, 3, 2, 13, 10, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23]]]
private def sourcePermutation (k : Fin 4) (j : Fin 5) : Equiv.Perm (Fin 24) where
  toFun := sourcePoint k j
  invFun := sourcePoint k j
  left_inv := by revert k j; decide +kernel
  right_inv := by revert k j; decide +kernel

private theorem sourceGenerator_val (k : Fin 4) (j : Fin 5) :
    (sourceGenerator k j).val = sourcePermutation k j := by
  fin_cases k
  all_goals revert j; decide +kernel

private def fusionTable : Fin 6 → Fin 24 → Fin 24 :=
![![0, 1, 13, 21, 4, 17, 22, 15, 16, 20, 12, 3, 2, 23, 8, 14, 5, 7, 11, 18, 10, 6, 19, 9], ![0, 1, 19, 20, 16, 8, 9, 4, 14, 13, 12, 6, 23, 3, 7, 15, 17, 5, 11, 10, 18, 2, 21, 22], ![0, 1, 13, 21, 4, 17, 22, 15, 16, 20, 12, 3, 2, 23, 8, 14, 5, 7, 11, 18, 10, 6, 19, 9], ![0, 1, 3, 2, 4, 15, 19, 14, 17, 11, 21, 6, 23, 10, 5, 7, 16, 8, 13, 9, 22, 18, 12, 20], ![0, 1, 2, 3, 4, 7, 21, 15, 17, 10, 12, 22, 9, 20, 14, 5, 8, 16, 11, 6, 23, 19, 18, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
private def fusionInverse : Fin 6 → Fin 24 → Fin 24 :=
![![0, 1, 12, 11, 4, 16, 21, 17, 14, 23, 20, 18, 10, 2, 15, 7, 8, 5, 19, 22, 9, 3, 6, 13], ![0, 1, 21, 13, 7, 17, 11, 14, 5, 6, 19, 18, 10, 9, 8, 15, 4, 16, 20, 2, 3, 22, 23, 12], ![0, 1, 12, 11, 4, 16, 21, 17, 14, 23, 20, 18, 10, 2, 15, 7, 8, 5, 19, 22, 9, 3, 6, 13], ![0, 1, 3, 2, 4, 14, 11, 15, 17, 19, 13, 9, 22, 18, 7, 5, 16, 8, 21, 6, 23, 10, 20, 12], ![0, 1, 2, 3, 4, 15, 19, 5, 16, 12, 9, 18, 10, 23, 14, 7, 17, 8, 22, 21, 13, 6, 11, 20], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
private def fusionPermutation (k : Fin 6) : Equiv.Perm (Fin 24) where
  toFun := fusionTable k
  invFun := fusionInverse k
  left_inv := by revert k; decide +kernel
  right_inv := by revert k; decide +kernel
private def fusionWord : Fin 6 → List (Fin 4) :=
![[1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1], [2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1], [3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1], [1, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1], [2, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3, 0, 1, 0, 1], []]
private theorem fusion_word : ∀ k,
    evalWord ElementaryEightGeometry.alphabet (fusionWord k) = fusionPermutation k := by
  decide +kernel

private def fusionConjugator (k : Fin 6) : StarGroup := ⟨fusionPermutation k, by
  rw [← fusion_word]
  apply StarOrderCertificate.word_mem ElementaryEightGeometry.alphabet StarGroup
  intro j
  fin_cases j
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact StarGroup.inv_mem (subset_closure (by simp))
  · exact StarGroup.inv_mem (subset_closure (by simp))⟩

private theorem fusionConjugator_mem (k : Fin 6) : fusionConjugator k ∈ imageContainer := by
  constructor
  · apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    revert k
    decide +kernel
  · change fusionConjugator k • InvolutionCentralizers.Second.starPair =
      InvolutionCentralizers.Second.starPair
    revert k
    decide +kernel

private def rowChoice : Fin 6 → Fin 4 := ![0, 3, 2, 0, 0, 1]
private def generatorMask : Fin 6 → Fin 5 → Fin 32 := ![![9, 14, 13, 11, 16], ![4, 5, 3, 11, 0], ![5, 7, 6, 8, 0], ![10, 8, 9, 25, 0], ![8, 10, 9, 25, 0], ![2, 4, 1, 9, 0]]

private theorem generator_fusion_point : ∀ (k : Fin 6) (j : Fin 5) (x : Fin 24),
    point (rowIndex k ⟨2 ^ j.val, by have := j.isLt; interval_cases j.val <;> decide⟩) x =
    (MulAut.conj (fusionPermutation k)
      (binaryProduct (sourcePermutation (rowChoice k))
        (fun i => (generatorMask k j).val.testBit i.val))) x := by decide +kernel

private theorem generator_fusion (k : Fin 6) (j : Fin 5) :
    rowGenerator k j = MulAut.conj (fusionConjugator k)
      (binaryProduct (sourceGenerator (rowChoice k))
        (fun i => (generatorMask k j).val.testBit i.val)) := by
  apply Subtype.ext
  change (rowGenerator k j).val = (fusionConjugator k).val *
    StarGroup.subtype (binaryProduct (sourceGenerator (rowChoice k))
      (fun i => (generatorMask k j).val.testBit i.val)) * (fusionConjugator k).val⁻¹
  rw [map_binaryProduct]
  simp only [subtype_apply, sourceGenerator_val]
  apply Equiv.ext
  intro x
  rw [rowGenerator,element_apply]
  exact generator_fusion_point k j x

/-- Each Sylow container maps into one of the four native source containers
by a conjugator preserving both original markings. -/
private theorem rowGroup_source_placement (k : Fin 6) :
    rowGroup k ≤ (sourceRow (rowChoice k)).map (MulAut.conj (fusionConjugator k)).toMonoidHom := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  refine ⟨binaryProduct (sourceGenerator (rowChoice k))
    (fun i => (generatorMask k j).val.testBit i.val),
    binaryProduct_mem _ _ _ (sourceGenerator_mem (rowChoice k)),?_⟩
  exact (generator_fusion k j).symm

/-- Exhaustive whole-subgroup placement in four literal quotient containers,
with a conjugator in the original marked centralizer. -/
theorem elementary_container_source_rows (A : Subgroup StarGroup)
    [IsElementaryAbelian 2 A] (hA : A ≤ imageContainer) :
    ∃ (k : Fin 4) (g : imageContainer),
      A ≤ (sourceRow k).map (MulAut.conj (g : StarGroup)).toMonoidHom := by
  obtain ⟨u,hu⟩ := elementary_container_placement A hA
  let B := A.map (MulAut.conj (u : StarGroup)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : B ≤ candidate := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hu hx
    rw [← he]
    simpa [MulAut.conj_apply, mul_assoc] using hy
  obtain ⟨k,hk⟩ := elementary_sylow_rows B hB
  let v : imageContainer := ⟨fusionConjugator k,fusionConjugator_mem k⟩
  refine ⟨rowChoice k,u*v,?_⟩
  intro x hx
  obtain ⟨y,hy,he⟩ := rowGroup_source_placement k
    (hk (mem_map_of_mem (MulAut.conj (u : StarGroup)⁻¹).toMonoidHom hx))
  refine ⟨y,hy,?_⟩
  have he' := congrArg (MulAut.conj (u : StarGroup)) he
  simpa [MulAut.conj_apply,mul_assoc,v] using he'

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
