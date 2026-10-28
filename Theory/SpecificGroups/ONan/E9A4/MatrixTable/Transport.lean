module

public import Theory.SpecificGroups.ONan.E9A4.Separation
public import Mathlib.Algebra.Field.ZMod

/-!
# Transport of the O'Nan E₉ × A₄ matrix table

Starting at the identity matrix, follow a word through the coordinate table.
The checked transitions identify its linear evaluation with the endpoint
matrix up to a nonzero scalar. The source-coordinate theorem identifies the
endpoint of each canonical word. Passing to PGL gives the actual word
transitions, and the five-entry separation certificate gives injectivity.

This module isolates the transport argument from finite multiplication checks.
Its consumer `MatrixTable.lean` discharges both table premises. Only realization
of the four generator matrices remains with the independent word certificate.
Sources: Aschbacher--Smith A.2.19; ATLAS matrices and words, `../source/README.md`.
-/

public section

namespace ONan.E9A4

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open Theory.GroupTheory
open Theory.SpecificGroups.E9A4 (Coord next words)

private theorem project_eq_of_matrix_smul {g h : Linear} {s : ZMod 7}
    (hs : s ≠ 0) (he : (g : Mat) = s • (h : Mat)) :
    Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk h := by
  symm
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 s hs, ?_⟩
  apply Units.ext
  change (h : Mat) * Matrix.scalar (Fin 45) s = (g : Mat)
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  exact he.symm

private theorem project_eq_of_common_matrix {g h : Linear} {M : Mat}
    {s t : ZMod 7} (hs : s ≠ 0) (ht : t ≠ 0)
    (hg : (g : Mat) = s • M) (hh : (h : Mat) = t • M) :
    Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk h := by
  apply project_eq_of_matrix_smul (div_ne_zero hs ht) (s := s / t)
  rw [hg, hh, smul_smul, div_mul_cancel₀ _ ht]

private theorem fold_words (c : Coord) :
    (words c).foldl next ((0, 0), 0) = c := by
  have hf (w : List (Fin 4)) (d : Coord) :
      Theory.SpecificGroups.E9A4.sourceForm (w.foldl next d) =
        Theory.SpecificGroups.E9A4.sourceForm d *
          evalWord Theory.SpecificGroups.E9A4.generators w := by
    induction w generalizing d with
    | nil => simp [evalWord]
    | cons i w ih =>
      simp only [List.foldl_cons, ih, Theory.SpecificGroups.E9A4.next_spec,
        evalWord, mul_assoc]
  apply Theory.SpecificGroups.E9A4.sourceEquiv.injective
  change Theory.SpecificGroups.E9A4.sourceForm _ = Theory.SpecificGroups.E9A4.sourceForm c
  rw [hf, Theory.SpecificGroups.E9A4.words_spec]
  exact one_mul _

variable (hgen : ∀ i, (linearGenerators i : Mat) = Data.generatorMatrix i)
  (htab : ∀ c i, Data.table c * Data.generatorMatrix i = Data.scalar c i • Data.table (next c i))
  (hscalar : ∀ c i, Data.scalar c i ≠ 0)

include hgen htab hscalar in
private theorem path_matrix (w : List (Fin 4)) (c : Coord) :
    ∃ s : ZMod 7, s ≠ 0 ∧
      Data.table c * ((evalWord linearGenerators w : Linear) : Mat) =
        s • Data.table (w.foldl next c) := by
  induction w generalizing c with
  | nil => exact ⟨1, one_ne_zero, by simp [evalWord]⟩
  | cons i w ih =>
    obtain ⟨s, hs, he⟩ := ih (next c i)
    refine ⟨Data.scalar c i * s, mul_ne_zero (hscalar c i) hs, ?_⟩
    change Data.table c * ((linearGenerators i : Mat) * ((evalWord linearGenerators w : Linear) : Mat)) = _
    rw [← mul_assoc, hgen, htab, smul_mul_assoc, he, smul_smul]
    rfl

include hgen htab hscalar in
private theorem normal_matrix (c : Coord) :
    ∃ s : ZMod 7, s ≠ 0 ∧
      ((Theory.SpecificGroups.E9A4.normalForm linearGenerators c : Linear) : Mat) = s • Data.table c := by
  obtain ⟨s, hs, he⟩ := path_matrix hgen htab hscalar (words c) ((0, 0), 0)
  rw [Data.table_zero, one_mul, fold_words] at he
  exact ⟨s, hs, he⟩

private theorem project_normal (c : Coord) :
    Matrix.ProjGenLinGroup.mk (Theory.SpecificGroups.E9A4.normalForm linearGenerators c) =
      (normalForm c).val := by
  rw [Theory.SpecificGroups.E9A4.normalForm, map_evalWord]
  simp only [project_linearGenerators]
  exact (map_evalWord ONan.matrixSubgroup.subtype generators (words c)).symm

include hgen htab hscalar in
theorem MatrixTable.normalForm_next_of_table (c : Coord) (i : Fin 4) : normalForm (next c i) = normalForm c * generators i := by
  obtain ⟨s, hs, he⟩ := normal_matrix hgen htab hscalar c
  obtain ⟨t, ht, hf⟩ := normal_matrix hgen htab hscalar (next c i)
  have hm : ((Theory.SpecificGroups.E9A4.normalForm linearGenerators c * linearGenerators i : Linear) : Mat) =
      (s * Data.scalar c i) • Data.table (next c i) := by
    change ((Theory.SpecificGroups.E9A4.normalForm linearGenerators c : Linear) : Mat) * (linearGenerators i : Mat) = _
    rw [he, hgen, smul_mul_assoc, htab, smul_smul]
  have hp := project_eq_of_common_matrix ht (mul_ne_zero hs (hscalar c i)) hf hm
  apply Subtype.ext
  change (normalForm (next c i)).val = (normalForm c).val * (generators i).val
  simpa only [map_mul, project_normal, project_linearGenerators] using hp

include hgen htab hscalar in
theorem MatrixTable.normalForm_injective_of_table : Function.Injective normalForm := by
  intro c d h
  obtain ⟨s, hs, he⟩ := normal_matrix hgen htab hscalar c
  obtain ⟨t, ht, hf⟩ := normal_matrix hgen htab hscalar d
  have hp : Matrix.ProjGenLinGroup.mk (Theory.SpecificGroups.E9A4.normalForm linearGenerators c) =
      Matrix.ProjGenLinGroup.mk (Theory.SpecificGroups.E9A4.normalForm linearGenerators d) := by
    rw [project_normal, project_normal, h]
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hm := congrArg (fun g : Linear => (g : Mat)) hu
  change ((Theory.SpecificGroups.E9A4.normalForm linearGenerators c : Linear) : Mat) *
      Matrix.scalar (Fin 45) u.val = ((Theory.SpecificGroups.E9A4.normalForm linearGenerators d : Linear) : Mat) at hm
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, he, hf, smul_smul] at hm
  apply Data.table_separates c d ((u.val * s)⁻¹ * t)
  have hn := congrArg (fun M : Mat => (u.val * s)⁻¹ • M) hm
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero u.ne_zero hs), one_smul] using hn

end ONan.E9A4
