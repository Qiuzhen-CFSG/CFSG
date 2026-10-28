module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Translations
public import Theory.Representation.MathieuCodeRestriction.Orthogonality
public import Theory.ElementaryAbelian.Basic

/-!
# The zero-sum condition on native trio translations

Three dot products of native Golay rows recover the three coordinates of
the sum of the translation vectors. Self-orthogonality of the code forces
this sum to vanish. Each octad identity is checked on its eight vectors.

Source: Aschbacher–Smith H.14.1(3), printed pp.396–397; Aschbacher,
*Sporadic Groups*, Lemma 20.2.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped BigOperators
namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section
abbrev Stabilizer := trioStabilizer standardTrio
abbrev Kernel := pCore 2 Stabilizer
private def leftRow : Fin 3 → Fin 12 := ![0, 0, 2]
private def rightRow : Fin 3 → Fin 12 := ![2, 5, 8]
private def rowConstant : Fin 3 → Fin 3 → ZMod 2 :=
  ![![1, 1, 0], ![0, 1, 1], ![1, 0, 1]]
private lemma row_pair (i j : Fin 3) (t : Vector) :
    (∑ v : Vector, row (rightRow j) (point (i,v)) *
      row (leftRow j) (point (i,v + t))) = t j + rowConstant i j := by
  revert i j t
  decide +kernel
private lemma rowConstant_sum (j : Fin 3) : ∑ i, rowConstant i j = 0 := by
  revert j
  decide +kernel
lemma translation_sum_zero (g : Stabilizer) (t : Fin 3 → Vector)
    (ht : ∀ i v, g.val.val (point (i,v)) = point (i,v + t i)) :
    ∑ i, t i = 0 := by
  funext j
  have h := golay_le_orthogonal (golay_invariant g.val⁻¹ (row_mem (leftRow j)))
    (row (rightRow j)) (row_mem (rightRow j))
  change (∑ x : Fin 24, row (rightRow j) x *
    row (leftRow j) (g.val.val x)) = 0 at h
  rw [← Equiv.sum_comp point] at h
  rw [Fintype.sum_prod_type] at h
  simp_rw [ht, row_pair] at h
  rw [Finset.sum_add_distrib, rowConstant_sum, add_zero] at h
  exact h
end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction