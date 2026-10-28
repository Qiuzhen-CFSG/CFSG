module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Checks

/-!
# Literal centralizers of the two inner E16 subgroups

The four certified elements of each candidate are lifted through the original
M22 embedding. Commutation in the actual outer Sylow implies the finite
three-coordinate tests. The resulting permutation membership is then
converted back into the intrinsic outer hexad core or outer translations.
These are the two centralizer bounds consumed by the outer E32 classification.

Source: Aschbacher--Smith H.14.3(1), printed p.397.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow

private def basisElement (k : Fin 2) (j : Fin 4) : M22 :=
  ((row_inner_iff (basisIndex k j)).mpr (basis_deleted k j)).choose

private theorem basisElement_embedding (k : Fin 2) (j : Fin 4) :
    m22Embedding (basisElement k j) = row (basisIndex k j) :=
  ((row_inner_iff (basisIndex k j)).mpr (basis_deleted k j)).choose_spec

private theorem basisElement_hexad (j : Fin 4) :
    basisElement 0 j ∈ m22InnerHexadKernel m22SourceOctad := by
  have h : row (basisIndex 0 j) ∈ octadPointwiseKernel m22SourceOctad := by
    apply (mem_octadPointwiseKernel _ _).mpr
    intro x hx
    exact (row_apply _ _).trans (hexad_basis j x hx)
  rw [← Hexad.inner_kernel_image] at h
  obtain ⟨v, hv, he⟩ := h
  have he' : v = basisElement 0 j :=
    m22Embedding_injective (he.trans (basisElement_embedding 0 j).symm)
  exact he' ▸ hv

private theorem basisElement_translation (j : Fin 4) :
    basisElement 1 j ∈ Sextet.innerTranslations := by
  change m22Embedding (basisElement 1 j) ∈ Sextet.sourceCore
  rw [basisElement_embedding]
  obtain ⟨t, ht⟩ := translation_basis j
  exact (mem_sourceCore _).mpr ⟨t, congrArg row ht⟩

/-- In the outer Sylow, an element centralizing the inner hexad core already
belongs to the outer hexad core. This is a literal permutation centralizer. -/
theorem centralizer_hexad (g : m22PairStabilizer) (hg : g ∈ outer.toSubgroup)
    (hc : ∀ x ∈ m22InnerHexadKernel m22SourceOctad,
      g.val * m22Embedding x = m22Embedding x * g.val) :
    g ∈ m22OuterHexadKernel m22SourceOctad := by
  obtain ⟨i, hi⟩ := row_surjective g.val hg
  have ht : ∀ (j : Fin 4) (x : Fin 3),
      point i (point (basisIndex 0 j) (testPoint x)) =
        point (basisIndex 0 j) (point i (testPoint x)) := by
    intro j x
    have he := congrArg (fun z : M24 => z.val (testPoint x))
      (hc (basisElement 0 j) (basisElement_hexad j))
    rw [basisElement_embedding, ← hi] at he
    change (row i).val ((row (basisIndex 0 j)).val (testPoint x)) =
      (row (basisIndex 0 j)).val ((row i).val (testPoint x)) at he
    simpa only [row_apply] using he
  have hp := hexad_centralizer_check i ((row_outer_iff i).mp (hi.symm ▸ g.property)) ht
  have hm : g.val ∈ octadPointwiseKernel m22SourceOctad := by
    apply (mem_octadPointwiseKernel _ _).mpr
    intro x hx
    rw [← hi]
    exact (row_apply _ _).trans (hp x hx)
  rw [← Hexad.outer_kernel_image] at hm
  obtain ⟨v, hv, hvx⟩ := hm
  exact (Subtype.ext hvx : v = g) ▸ hv

/-- The centralizer of the inner translations in the outer Sylow consists of
outer translations; its ambient embedding is the original pair inclusion. -/
theorem centralizer_translations (g : m22PairStabilizer) (hg : g ∈ outer.toSubgroup)
    (hc : ∀ x ∈ Sextet.innerTranslations,
      g.val * m22Embedding x = m22Embedding x * g.val) :
    g ∈ Sextet.outerTranslations := by
  obtain ⟨i, hi⟩ := row_surjective g.val hg
  have ht : ∀ (j : Fin 4) (x : Fin 3),
      point i (point (basisIndex 1 j) (testPoint x)) =
        point (basisIndex 1 j) (point i (testPoint x)) := by
    intro j x
    have he := congrArg (fun z : M24 => z.val (testPoint x))
      (hc (basisElement 1 j) (basisElement_translation j))
    rw [basisElement_embedding, ← hi] at he
    change (row i).val ((row (basisIndex 1 j)).val (testPoint x)) =
      (row (basisIndex 1 j)).val ((row i).val (testPoint x)) at he
    simpa only [row_apply] using he
  obtain ⟨t, ht⟩ := translation_centralizer_check i
    ((row_outer_iff i).mp (hi.symm ▸ g.property)) ht
  exact (mem_sourceCore _).mpr ⟨t, (congrArg row ht).trans hi⟩

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
