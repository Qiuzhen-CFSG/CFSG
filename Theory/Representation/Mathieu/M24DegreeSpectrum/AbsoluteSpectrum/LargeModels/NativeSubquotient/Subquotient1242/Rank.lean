module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Leading
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Data

/-!
# Injectivity of the saved native 1242 source embedding

The 1474 saved columns have distinct leading positions in the 1936-dimensional
ambient space. Their checked leading remainders and distinct positions prove
injectivity by triangular elimination. No retraction matrix is needed. This
establishes rank only; both generator invariance equations remain necessary
before the source can carry the restricted native action.
-/

set_option Elab.async false
public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Leading Degree220Pair.NativeActions.CertificatePacked

private theorem positions_length : leadingPositions.length = 1474 := by decide +kernel
private theorem rows_length : embeddingTransposeRows.length = 1474 := by decide +kernel
private theorem positions_nodup : leadingPositions.Nodup :=
  (checkDistinct_sound leadingPositions 0 (by decide +kernel)).1
private theorem positions_bound : leadingPositions.all (fun k => decide (k < 1936)) = true := by
  decide +kernel
private theorem leading_checked : checkLeading embeddingTransposeRows leadingPositions = true := by
  decide +kernel

private def pivot (j : Fin 1474) : Fin 1936 :=
  ⟨leadingPositions[j.val]!, by
    have hj : j.val < leadingPositions.length := by rw [positions_length]; exact j.isLt
    have h := List.all_eq_true.mp positions_bound _ (List.getElem_mem hj)
    simpa [List.getElem!_eq_getElem?_getD, hj] using h⟩

private theorem pivot_injective : Function.Injective pivot := by
  intro i j h
  have hi : i.val < leadingPositions.length := by rw [positions_length]; exact i.isLt
  have hj : j.val < leadingPositions.length := by rw [positions_length]; exact j.isLt
  have he := congrArg Fin.val h
  change leadingPositions[i.val]! = leadingPositions[j.val]! at he
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at he
  exact Fin.ext (positions_nodup.getElem_inj_iff.mp he)

/-- The literal saved source map has full column rank. Source invariance is a
separate obligation; this theorem does not treat a coordinate slice as an action. -/
theorem embedding_injective : Function.Injective (Matrix.toLin' embedding) := by
  apply injective_of_leading embedding pivot pivot_injective
  · intro j
    have h := leading_bit embeddingTransposeRows[j.val]! leadingPositions[j.val]!
      (checkLeading_sound _ _ leading_checked j.val (by rw [rows_length]; exact j.isLt))
    exact h.1
  · intro i j hij
    have h := leading_bit embeddingTransposeRows[j.val]! leadingPositions[j.val]!
      (checkLeading_sound _ _ leading_checked j.val (by rw [rows_length]; exact j.isLt))
    exact h.2 i.val hij
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
