module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Native

/-!
# Fusion and extension of the native M22 elementary-eight rows

Of the four E8 containers in the certified Sylow, rows zero and three are
conjugate in that Sylow, as are rows one and two. An explicit word fixing the
M22 point embeds row one in an E16. The aligned M22 image is the full point
stabilizer, so all these conjugations lift through the original native marking.
The six-container placement therefore reduces to the two source E16 kernels
and one fixed E8. This identifies the elementary-subgroup alternatives; it
does not yet identify the E8 automizer or the nontrivial J4 inverse-image cases.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1,
pp.489--490. The underlying permutation and ATLAS word certificates are reused
from M23's `Involutions.Fusion`; the additional short word and point equations
are checked by Lean's kernel.
-/

public noncomputable section
open Subgroup Sporadic.Mathieu Theory.GroupTheory MathieuCode
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open M23Geometry FusionCertificate ElementarySylow M22ChapterH M22ChapterH.CompatibleSylow

private def ambientWord (w : List (Fin 6)) : M23 :=
  ⟨Theory.GroupTheory.evalWord ambientGen w, by
    induction w with
    | nil => exact M23.one_mem
    | cons i w ih => exact M23.mul_mem (ambientGen_mem i) ih⟩

/-- A literal M23 word fixing the aligned M22 point and extending the second E8. -/
def bigConjugator : M23 :=
  ambientWord ([2,2,2,2,2] ++ [1,1,0,1] ++ [5,5,5,5,5])

private def bigTable : Fin 23 → Fin 23 :=
  ![0, 13, 18, 21, 17, 16, 1, 4, 5, 8, 11, 6, 9, 22, 2, 7, 19, 20, 12, 3, 10, 14, 15]

private theorem bigConjugator_points : ∀ x : Fin 23,
    (bigConjugator : Equiv.Perm (Fin 23)) x = bigTable x := by decide +kernel

private theorem bigConjugator_fixed : (bigConjugator : Equiv.Perm (Fin 23)) 0 = 0 :=
  bigConjugator_points 0

attribute [local irreducible] bigConjugator

private def bigIndex : Fin 8 → Fin 16 := ![0,6,5,3,1,7,4,2]

private theorem large_points : ∀ (i : Fin 8) (x : Fin 23),
    bigTable (pointTable (smallIndex 1 i) x) =
      pointTable (candidateIndex 0 (bigIndex i)) (bigTable x) := by decide +kernel

private theorem two_points : ∀ (i : Fin 8) (x : Fin 23),
    pointTable 2 (pointTable (smallIndex 1 i) x) =
      pointTable (smallIndex 2 (![0,1,4,5,7,6,3,2] i)) (pointTable 2 x) := by decide +kernel

private theorem three_points : ∀ (i : Fin 8) (x : Fin 23),
    pointTable 8 (pointTable (smallIndex 0 i) x) =
      pointTable (smallIndex 3 (![0,1,6,7,2,3,4,5] i)) (pointTable 8 x) := by decide +kernel

/-- The actual M23 element at a certified Sylow index. -/
@[expose] def sylowElement (i : Fin 128) : M23 :=
  ⟨perm i,rawSubgroup_le (perm_mem i)⟩

private theorem conjugate_small_of_points (k l : Fin 4) (g : M23) (f : Fin 8 → Fin 8)
    (h : ∀ (i : Fin 8) (x : Fin 23),
      g.val (pointTable (smallIndex k i) x) = pointTable (smallIndex l (f i)) (g.val x)) :
    (small k).map (MulAut.conj g).toMonoidHom = small l := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨y,⟨i,hi⟩,rfl⟩
    refine ⟨f i,?_⟩
    change perm (smallIndex k i) = y.val at hi
    apply Equiv.ext
    intro x
    change pointTable (smallIndex l (f i)) x = g.val (y.val (g.val.symm x))
    rw [← hi]
    change pointTable (smallIndex l (f i)) x = g.val (pointTable (smallIndex k i) (g.val.symm x))
    have he := h i (g.val.symm x)
    rw [Equiv.apply_symm_apply] at he
    exact he.symm
  · rw [card_map_of_injective (MulAut.conj g).injective,small_card,small_card]

/-- Rows two and one are conjugate inside the actual Sylow subgroup. -/
theorem small_two_conjugate :
    (small 1).map (MulAut.conj (sylowElement 2)).toMonoidHom = small 2 :=
  conjugate_small_of_points 1 2 _ _ two_points

/-- Rows three and zero are conjugate inside the actual Sylow subgroup. -/
theorem small_three_conjugate :
    (small 0).map (MulAut.conj (sylowElement 8)).toMonoidHom = small 3 :=
  conjugate_small_of_points 0 3 _ _ three_points

/-- The second E8 row extends to an actual E16 after an explicit conjugation
fixing the M22 point. -/
theorem small_one_extends :
    (small 1).map (MulAut.conj bigConjugator).toMonoidHom ≤ candidate 0 := by
  rintro _ ⟨y,⟨i,hi⟩,rfl⟩
  refine ⟨bigIndex i,?_⟩
  change perm (smallIndex 1 i) = y.val at hi
  apply Equiv.ext
  intro x
  change pointTable (candidateIndex 0 (bigIndex i)) x =
    bigConjugator.val (y.val (bigConjugator.val.symm x))
  rw [← hi]
  have he := large_points i (bigConjugator.val.symm x)
  rw [← bigConjugator_points, ← bigConjugator_points,Equiv.apply_symm_apply] at he
  exact he.symm


private theorem sylowElement_fixed (i : Fin 128) :
    (sylowElement i : Equiv.Perm (Fin 23)) 0 = 0 := by
  change pointTable i 0 = 0
  revert i
  decide +kernel

private theorem conjugation_map (B : Subgroup M22) (g : M22) :
    (B.map (MulAut.conj g).toMonoidHom).map alignedEmbedding =
      (B.map alignedEmbedding).map (MulAut.conj (alignedEmbedding g)).toMonoidHom := by
  rw [map_map,map_map]
  apply congrArg (fun f : M22 →* M23 => B.map f)
  apply MonoidHom.ext
  intro x
  change alignedEmbedding (g*x*g⁻¹) = alignedEmbedding g * alignedEmbedding x * (alignedEmbedding g)⁻¹
  simp only [map_mul,map_inv]

/-- The first and fourth Sylow rows are conjugate in native M22, with the
actual aligned permutation conjugator retained. -/
theorem smallContainer_three_fusion : ∃ g : M22,
    alignedEmbedding g = sylowElement 8 ∧
    (smallContainer 0).map (MulAut.conj g).toMonoidHom = smallContainer 3 := by
  have hg : sylowElement 8 ∈ alignedEmbedding.range := by
    rw [alignedEmbedding_range]
    exact sylowElement_fixed 8
  obtain ⟨g,hg⟩ := hg
  refine ⟨g,hg,?_⟩
  apply Subgroup.map_injective alignedEmbedding_injective
  rw [conjugation_map,smallContainer_map,smallContainer_map,hg,small_three_conjugate]

/-- The other two Sylow E8 rows are conjugate in native M22. -/
theorem smallContainer_two_fusion : ∃ g : M22,
    alignedEmbedding g = sylowElement 2 ∧
    (smallContainer 1).map (MulAut.conj g).toMonoidHom = smallContainer 2 := by
  have hg : sylowElement 2 ∈ alignedEmbedding.range := by
    rw [alignedEmbedding_range]
    exact sylowElement_fixed 2
  obtain ⟨g,hg⟩ := hg
  refine ⟨g,hg,?_⟩
  apply Subgroup.map_injective alignedEmbedding_injective
  rw [conjugation_map,smallContainer_map,smallContainer_map,hg,small_two_conjugate]

/-- The first certified permutation E16 is the image of one of the two
literal source kernels under the aligned native embedding. -/
theorem large_candidate_native :
    ∃ B : Subgroup M22, B.map alignedEmbedding = candidate 0 ∧
      (B = m22InnerHexadKernel m22SourceOctad ∨ B = Sextet.innerTranslations) := by
  let B := (candidate 0).comap alignedEmbedding
  have hBS : B ≤ inner.toSubgroup := by
    have h := comap_mono (f := alignedEmbedding) (candidate_le_sylow 0)
    rw [← alignedEmbedding_sylow,comap_map_eq_self_of_injective alignedEmbedding_injective] at h
    exact h
  have hmap : B.map alignedEmbedding = candidate 0 := by
    rw [map_comap_eq,inf_eq_right]
    exact (candidate_le_sylow 0).trans (alignedEmbedding_sylow ▸ map_le_range alignedEmbedding inner.toSubgroup)
  let := candidate_elementary 0
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.comap_of_injective
    alignedEmbedding alignedEmbedding_injective _
  have hc : Nat.card B = 16 := by
    rw [← card_map_of_injective alignedEmbedding_injective,hmap,candidate_card]
  exact ⟨B,hmap,inner_card16 B inferInstance hc hBS⟩

/-- The extendible E8 row is contained in a conjugate of one of the existing
source E16 kernels; the extension is proved by an actual M22 element. -/
theorem smallContainer_one_extension : ∃ g : M22,
    smallContainer 1 ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
    smallContainer 1 ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom := by
  have hg : bigConjugator ∈ alignedEmbedding.range := by
    rw [alignedEmbedding_range]
    exact bigConjugator_fixed
  obtain ⟨g,hg⟩ := hg
  obtain ⟨B,hmap,hB⟩ := large_candidate_native
  have hle : (smallContainer 1).map (MulAut.conj g).toMonoidHom ≤ B := by
    apply (Subgroup.map_le_map_iff_of_injective alignedEmbedding_injective).mp
    rw [conjugation_map,smallContainer_map,hmap,hg]
    exact small_one_extends
  have hback : smallContainer 1 ≤ B.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨(MulAut.conj g) x,hle (mem_map_of_mem _ hx),?_⟩
    simp [mul_assoc]
  refine ⟨g⁻¹,?_⟩
  rcases hB with rfl | rfl
  · exact Or.inl hback
  · exact Or.inr hback

private theorem conjugate_comp (B : Subgroup M22) (g h : M22) :
    (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  apply congrArg (fun f : M22 →* M22 => B.map f)
  apply MonoidHom.ext
  intro x
  change g*(h*x*h⁻¹)*g⁻¹ = (g*h)*x*(g*h)⁻¹
  simp [mul_assoc]

/-- Each of the four saved E8 rows reduces to one genuine E8 row or an existing
source E16 kernel. This is a conjugacy statement in M22 itself. -/
theorem smallContainer_three_cases (k : Fin 4) : ∃ g : M22,
    smallContainer k ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
    smallContainer k ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom ∨
    smallContainer k ≤ (smallContainer 0).map (MulAut.conj g).toMonoidHom := by
  fin_cases k
  · refine ⟨1,Or.inr (Or.inr ?_)⟩
    intro x hx
    exact ⟨x,hx,by simp⟩
  · obtain ⟨g,hg⟩ := smallContainer_one_extension
    exact ⟨g,hg.imp id Or.inl⟩
  · obtain ⟨g,_,hg⟩ := smallContainer_two_fusion
    obtain ⟨h,hh⟩ := smallContainer_one_extension
    refine ⟨g*h,?_⟩
    rcases hh with hh | hh
    · left
      have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hh
      rwa [hg,conjugate_comp] at ht
    · right; left
      have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hh
      rwa [hg,conjugate_comp] at ht
  · obtain ⟨g,_,hg⟩ := smallContainer_three_fusion
    exact ⟨g,Or.inr (Or.inr hg.ge)⟩

/-- Exhaustive native M22 elementary placement in exactly three actual source
containers: the hexad E16, sextet E16, and one fixed E8. No size or normality
premise is imposed on the input subgroup. -/
theorem elementary_native_three_cases (A : Subgroup M22) [IsElementaryAbelian 2 A] :
    ∃ g : M22,
      A ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom ∨
      A ≤ (smallContainer 0).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := elementary_native_cover A
  rcases hg with h | h | ⟨k,h⟩
  · exact ⟨g,Or.inl h⟩
  · exact ⟨g,Or.inr (Or.inl h)⟩
  · obtain ⟨n,hn⟩ := smallContainer_three_cases k
    have transfer (B : Subgroup M22)
        (hB : smallContainer k ≤ B.map (MulAut.conj n).toMonoidHom) :
        A ≤ B.map (MulAut.conj (g*n)).toMonoidHom := by
      have hh := h.trans (map_mono (f := (MulAut.conj g).toMonoidHom) hB)
      rwa [conjugate_comp] at hh
    exact ⟨g*n,hn.imp (transfer _) (fun hh => hh.imp (transfer _) (transfer _))⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
