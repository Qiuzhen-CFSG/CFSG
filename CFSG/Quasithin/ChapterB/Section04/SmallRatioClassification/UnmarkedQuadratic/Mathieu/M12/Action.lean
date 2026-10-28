module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Contracts
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coordinates
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Native
import all CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.NativeMatrices

/-!
# The literal Sylow matrices on the Aut(M12) heart

This internal calculation extension uses the already checked generator matrices
and their implementing equivalences. The intentional `import all` does not
expose their implementation in any public statement. The certified shorter-word
recurrences transport the generators to all 128 elements of the actual overlap.
The identification with Aut(M12), including its outer action, is unchanged.

Source: Aschbacher--Smith K.4.4, printed pp.459--460; the existing native
generators use the attributed ATLAS M12d2G1-p24B0 coordinates.
-/

public section
open Sporadic.Mathieu M12ExceptionalExtension OverlapExtensions
open CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
open Representation
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12

private theorem native_generator (j : Fin 2) :
    Ambient.automorphismRepresentation (automorphismEquiv (Ambient.NativeMatrices.generator j)) =
      (Ambient.NativeMatrices.heartEquiv j).toLinearMap := by
  exact congrArg LinearEquiv.toLinearMap
    (Ambient.heart_intertwiner_unique _ _ _ (Ambient.implementer_spec _)
      (Ambient.intertwines_of_original _ _ (Ambient.NativeMatrices.heart_intertwines j)))

noncomputable def coordinateRepresentation : Representation (ZMod 2) Carrier Coordinates :=
  (heartEquiv.symm.conjRingEquiv.toMonoidHom.comp Ambient.automorphismRepresentation).comp
    automorphismEquiv.toMonoidHom

theorem coordinate_generator (j : Fin 2) :
    coordinateRepresentation (Ambient.NativeMatrices.generator j) =
      (Data.baseMatrix j).mulVecLin := by
  change heartEquiv.symm.conjRingEquiv
    (Ambient.automorphismRepresentation (automorphismEquiv (Ambient.NativeMatrices.generator j))) = _
  rw [native_generator]
  apply LinearMap.ext
  intro v
  change heartEquiv.symm (heartEquiv ((Ambient.NativeMatrices.matrix j).mulVecLin
    (heartEquiv.symm (heartEquiv v)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl


theorem coordinate_equivariant (g : Carrier) (v : Coordinates) :
    heartEquiv (coordinateRepresentation g v) =
      Ambient.automorphismRepresentation (automorphismEquiv g) (heartEquiv v) := by
  change heartEquiv (heartEquiv.symm _) = _
  exact heartEquiv.apply_symm_apply _

open Data
private theorem evaluate_append {H : Type*} [Group H] {n : ℕ} (g : Fin n → H)
    (u v : List (Fin n)) :
    FiniteWords.evaluate g (u ++ v) = FiniteWords.evaluate g u * FiniteWords.evaluate g v := by
  induction u with
  | nil => simp [FiniteWords.evaluate]
  | cons j u ih => simp only [List.cons_append, FiniteWords.evaluate, ih, mul_assoc]

-- The following proof consumes the finite recurrence certificate.
theorem coordinate_prefix (i : Fin 90)
    (hcheck : ∀ i, prefixCheck i) :
    coordinateRepresentation
      (FiniteWords.evaluate Ambient.NativeMatrices.generator (prefixWord i)) =
      (prefixMatrix i).mulVecLin := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      rw [prefix_word_zero, FiniteWords.evaluate, map_one, prefix_zero, Matrix.mulVecLin_one]
      rfl
    · have step := hcheck i hi
      rw [step.2.1, evaluate_append, FiniteWords.evaluate, FiniteWords.evaluate, mul_one,
        map_mul, ih (prefixParent i) step.1, coordinate_generator]
      change (prefixMatrix (prefixParent i)).mulVecLin.comp
        (baseMatrix (prefixLast i)).mulVecLin = _
      rw [← Matrix.mulVecLin_mul, step.2.2]

private theorem generator_word (j : Fin 3) :
    (Overlap.generator j).val =
      FiniteWords.evaluate Ambient.NativeMatrices.generator (prefixWord (generatorEnd j)) := by
  apply Subtype.ext
  rw [Overlap.generator_val]
  revert j
  decide +kernel

private theorem generator_matrix : ∀ j : Fin 3,
    prefixMatrix (generatorEnd j) = generatorMatrix j := by decide +kernel

theorem coordinate_overlap_generator (hcheck : ∀ i, prefixCheck i) (j : Fin 3) :
    coordinateRepresentation (Overlap.generator j).val = (generatorMatrix j).mulVecLin := by
  rw [generator_word, coordinate_prefix _ hcheck, generator_matrix]

set_option maxRecDepth 4096 in
theorem coordinate_element (hprefix : ∀ i, prefixCheck i) (hcheck : ∀ i, matrixCheck i)
    (i : Fin 128) : coordinateRepresentation (Overlap.element i).val = (matrix i).mulVecLin := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      rw [Overlap.element_zero]
      change coordinateRepresentation 1 = _
      rw [map_one, matrix_zero, Matrix.mulVecLin_one]
      rfl
    · have step := hcheck i hi
      have he : Overlap.element i = Overlap.element (parent i) * Overlap.generator (last i) := by
        change FiniteWords.evaluate Overlap.generator _ = _
        rw [step.2.1, evaluate_append, FiniteWords.evaluate, FiniteWords.evaluate, mul_one]
        rfl
      rw [he]
      change coordinateRepresentation ((Overlap.element (parent i)).val *
        (Overlap.generator (last i)).val) = _
      rw [map_mul, ih (parent i) step.1, coordinate_overlap_generator hprefix]
      change (matrix (parent i)).mulVecLin.comp (generatorMatrix (last i)).mulVecLin = _
      rw [← Matrix.mulVecLin_mul, step.2.2]

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
