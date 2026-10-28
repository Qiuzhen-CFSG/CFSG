module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularC

/-!
# The literal Figure 2(a) quotient generators

The fourth printed permutation is certified in the native star group by a
word in its existing generators. Together with the first two (b) generators,
the first vertical (c) generator, and the marked Figure 1 pair, it gives the
whole (a) image. The MOG comparison fixes the printed coordinate convention.
This is the first container needed by the exhaustive nonsingular-image split.
Source: Kleidman--Wilson (1988), Figures 1/2 and Lemma 2.3.1, pp.486,490,492.
-/

set_option Elab.async false
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages.FigureA
open Subgroup Theory.GroupTheory Cardinality.QuotientCount.Image Cardinality.KernelCount
open ElementaryEightGeometry

def fourthTable : Fin 24 → Fin 24 := ![0, 1, 2, 3, 5, 4, 13, 17, 14, 18, 22, 11, 12, 6, 8, 16, 15, 7, 9, 19, 20, 23, 10, 21]
def fourthPermutation : Equiv.Perm (Fin 24) where
  toFun := fourthTable
  invFun := fourthTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def fourthMogTable : Fin 24 → Fin 24 := ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10, 18, 19, 20, 21, 23, 22, 12, 13, 14, 15, 17, 16]
def fourthMogPermutation : Equiv.Perm (Fin 24) where
  toFun := fourthMogTable
  invFun := fourthMogTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem fourth_mog : MulAut.conj mogToStar fourthMogPermutation = fourthPermutation := by
  decide +kernel

private def fourthWord : List (Fin 4) := [2, 3, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1]
private theorem fourth_word : evalWord ElementaryEightGeometry.alphabet fourthWord = fourthPermutation := by
  decide +kernel

def fourth : StarGroup := ⟨fourthPermutation,by
  rw [← fourth_word]
  apply StarOrderCertificate.word_mem ElementaryEightGeometry.alphabet StarGroup
  intro j
  fin_cases j
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact StarGroup.inv_mem (subset_closure (by simp))
  · exact StarGroup.inv_mem (subset_closure (by simp))⟩

def wholeGenerator : Fin 5 → StarGroup :=
  ![starElement 0,starElement 1,NonsingularC.vertical 0,fourth,starElement 5]
def wholeImage : Subgroup StarGroup := closure (Set.range wholeGenerator)

theorem wholeGenerator_mem (i : Fin 5) : wholeGenerator i ∈ wholeImage :=
  subset_closure (Set.mem_range_self i)

private theorem generator_square (i : Fin 5) : wholeGenerator i * wholeGenerator i = 1 := by
  apply Subtype.ext
  revert i
  decide +kernel
private theorem generator_commute (i j : Fin 5) : Commute (wholeGenerator i) (wholeGenerator j) := by
  apply Subtype.ext
  revert i j
  decide +kernel

instance wholeImage_elementary : IsElementaryAbelian 2 wholeImage := by
  let : IsMulCommutative (closure (Set.range wholeGenerator)) :=
    isMulCommutative_closure (by
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
      exact generator_commute i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨i,rfl⟩
  simpa only [pow_two] using generator_square i

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages.FigureA
