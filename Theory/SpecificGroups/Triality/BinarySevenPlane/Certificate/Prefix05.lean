module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Certificate.Prefix04

/-! The first 6 factors of the explicit Lang word on the full Geck lattice.
The sparse root-factor entries and every multiplication are kernel checked.
Source: the eleven-factor witness for the nonsplit torus at q = 2 (ATLAS p.89).
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane.Certificate
open Coefficients

def prefix5 : Matrix (Fin 28) (Fin 28) Scalar :=
  ![![⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨6⟩,⟨6⟩,⟨6⟩,⟨6⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨7⟩,⟨5⟩,⟨7⟩,⟨7⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩]]
private def factorColumns : Fin 28 → List (Fin 28 × Scalar) :=
  ![[(0,⟨1⟩),(11,⟨6⟩)],
    [(1,⟨1⟩),(11,⟨6⟩)],
    [(2,⟨1⟩),(11,⟨6⟩)],
    [(3,⟨1⟩),(11,⟨6⟩)],
    [(4,⟨1⟩),(17,⟨6⟩)],
    [(5,⟨1⟩),(19,⟨6⟩)],
    [(6,⟨1⟩)],
    [(7,⟨1⟩)],
    [(0,⟨6⟩),(1,⟨6⟩),(2,⟨6⟩),(3,⟨6⟩),(8,⟨1⟩),(11,⟨2⟩)],
    [(9,⟨1⟩)],
    [(10,⟨1⟩)],
    [(11,⟨1⟩)],
    [(12,⟨1⟩),(26,⟨6⟩)],
    [(13,⟨1⟩),(27,⟨6⟩)],
    [(14,⟨1⟩)],
    [(15,⟨1⟩)],
    [(6,⟨6⟩),(16,⟨1⟩)],
    [(17,⟨1⟩)],
    [(7,⟨6⟩),(18,⟨1⟩)],
    [(19,⟨1⟩)],
    [(20,⟨1⟩)],
    [(21,⟨1⟩)],
    [(22,⟨1⟩)],
    [(23,⟨1⟩)],
    [(14,⟨6⟩),(24,⟨1⟩)],
    [(15,⟨6⟩),(25,⟨1⟩)],
    [(26,⟨1⟩)],
    [(27,⟨1⟩)]]
private lemma factor_row_0 : ∀ j, (curve 7 ⟨6⟩ 0 j).val = (columnEntry (factorColumns j) 0).val := by decide +kernel
private lemma factor_row_1 : ∀ j, (curve 7 ⟨6⟩ 1 j).val = (columnEntry (factorColumns j) 1).val := by decide +kernel
private lemma factor_row_2 : ∀ j, (curve 7 ⟨6⟩ 2 j).val = (columnEntry (factorColumns j) 2).val := by decide +kernel
private lemma factor_row_3 : ∀ j, (curve 7 ⟨6⟩ 3 j).val = (columnEntry (factorColumns j) 3).val := by decide +kernel
private lemma factor_row_4 : ∀ j, (curve 7 ⟨6⟩ 4 j).val = (columnEntry (factorColumns j) 4).val := by decide +kernel
private lemma factor_row_5 : ∀ j, (curve 7 ⟨6⟩ 5 j).val = (columnEntry (factorColumns j) 5).val := by decide +kernel
private lemma factor_row_6 : ∀ j, (curve 7 ⟨6⟩ 6 j).val = (columnEntry (factorColumns j) 6).val := by decide +kernel
private lemma factor_row_7 : ∀ j, (curve 7 ⟨6⟩ 7 j).val = (columnEntry (factorColumns j) 7).val := by decide +kernel
private lemma factor_row_8 : ∀ j, (curve 7 ⟨6⟩ 8 j).val = (columnEntry (factorColumns j) 8).val := by decide +kernel
private lemma factor_row_9 : ∀ j, (curve 7 ⟨6⟩ 9 j).val = (columnEntry (factorColumns j) 9).val := by decide +kernel
private lemma factor_row_10 : ∀ j, (curve 7 ⟨6⟩ 10 j).val = (columnEntry (factorColumns j) 10).val := by decide +kernel
private lemma factor_row_11 : ∀ j, (curve 7 ⟨6⟩ 11 j).val = (columnEntry (factorColumns j) 11).val := by decide +kernel
private lemma factor_row_12 : ∀ j, (curve 7 ⟨6⟩ 12 j).val = (columnEntry (factorColumns j) 12).val := by decide +kernel
private lemma factor_row_13 : ∀ j, (curve 7 ⟨6⟩ 13 j).val = (columnEntry (factorColumns j) 13).val := by decide +kernel
private lemma factor_row_14 : ∀ j, (curve 7 ⟨6⟩ 14 j).val = (columnEntry (factorColumns j) 14).val := by decide +kernel
private lemma factor_row_15 : ∀ j, (curve 7 ⟨6⟩ 15 j).val = (columnEntry (factorColumns j) 15).val := by decide +kernel
private lemma factor_row_16 : ∀ j, (curve 7 ⟨6⟩ 16 j).val = (columnEntry (factorColumns j) 16).val := by decide +kernel
private lemma factor_row_17 : ∀ j, (curve 7 ⟨6⟩ 17 j).val = (columnEntry (factorColumns j) 17).val := by decide +kernel
private lemma factor_row_18 : ∀ j, (curve 7 ⟨6⟩ 18 j).val = (columnEntry (factorColumns j) 18).val := by decide +kernel
private lemma factor_row_19 : ∀ j, (curve 7 ⟨6⟩ 19 j).val = (columnEntry (factorColumns j) 19).val := by decide +kernel
private lemma factor_row_20 : ∀ j, (curve 7 ⟨6⟩ 20 j).val = (columnEntry (factorColumns j) 20).val := by decide +kernel
private lemma factor_row_21 : ∀ j, (curve 7 ⟨6⟩ 21 j).val = (columnEntry (factorColumns j) 21).val := by decide +kernel
private lemma factor_row_22 : ∀ j, (curve 7 ⟨6⟩ 22 j).val = (columnEntry (factorColumns j) 22).val := by decide +kernel
private lemma factor_row_23 : ∀ j, (curve 7 ⟨6⟩ 23 j).val = (columnEntry (factorColumns j) 23).val := by decide +kernel
private lemma factor_row_24 : ∀ j, (curve 7 ⟨6⟩ 24 j).val = (columnEntry (factorColumns j) 24).val := by decide +kernel
private lemma factor_row_25 : ∀ j, (curve 7 ⟨6⟩ 25 j).val = (columnEntry (factorColumns j) 25).val := by decide +kernel
private lemma factor_row_26 : ∀ j, (curve 7 ⟨6⟩ 26 j).val = (columnEntry (factorColumns j) 26).val := by decide +kernel
private lemma factor_row_27 : ∀ j, (curve 7 ⟨6⟩ 27 j).val = (columnEntry (factorColumns j) 27).val := by decide +kernel
private lemma factor_columns (i j) : curve 7 ⟨6⟩ i j = columnEntry (factorColumns j) i := by
  apply congrArg Scalar.mk
  fin_cases i
  · exact factor_row_0 j
  · exact factor_row_1 j
  · exact factor_row_2 j
  · exact factor_row_3 j
  · exact factor_row_4 j
  · exact factor_row_5 j
  · exact factor_row_6 j
  · exact factor_row_7 j
  · exact factor_row_8 j
  · exact factor_row_9 j
  · exact factor_row_10 j
  · exact factor_row_11 j
  · exact factor_row_12 j
  · exact factor_row_13 j
  · exact factor_row_14 j
  · exact factor_row_15 j
  · exact factor_row_16 j
  · exact factor_row_17 j
  · exact factor_row_18 j
  · exact factor_row_19 j
  · exact factor_row_20 j
  · exact factor_row_21 j
  · exact factor_row_22 j
  · exact factor_row_23 j
  · exact factor_row_24 j
  · exact factor_row_25 j
  · exact factor_row_26 j
  · exact factor_row_27 j
private lemma product_row_0 : ∀ j, ((factorColumns j).map (fun p => prefix4 0 p.1 * p.2)).sum.val = (prefix5 0 j).val := by decide +kernel
private lemma product_row_1 : ∀ j, ((factorColumns j).map (fun p => prefix4 1 p.1 * p.2)).sum.val = (prefix5 1 j).val := by decide +kernel
private lemma product_row_2 : ∀ j, ((factorColumns j).map (fun p => prefix4 2 p.1 * p.2)).sum.val = (prefix5 2 j).val := by decide +kernel
private lemma product_row_3 : ∀ j, ((factorColumns j).map (fun p => prefix4 3 p.1 * p.2)).sum.val = (prefix5 3 j).val := by decide +kernel
private lemma product_row_4 : ∀ j, ((factorColumns j).map (fun p => prefix4 4 p.1 * p.2)).sum.val = (prefix5 4 j).val := by decide +kernel
private lemma product_row_5 : ∀ j, ((factorColumns j).map (fun p => prefix4 5 p.1 * p.2)).sum.val = (prefix5 5 j).val := by decide +kernel
private lemma product_row_6 : ∀ j, ((factorColumns j).map (fun p => prefix4 6 p.1 * p.2)).sum.val = (prefix5 6 j).val := by decide +kernel
private lemma product_row_7 : ∀ j, ((factorColumns j).map (fun p => prefix4 7 p.1 * p.2)).sum.val = (prefix5 7 j).val := by decide +kernel
private lemma product_row_8 : ∀ j, ((factorColumns j).map (fun p => prefix4 8 p.1 * p.2)).sum.val = (prefix5 8 j).val := by decide +kernel
private lemma product_row_9 : ∀ j, ((factorColumns j).map (fun p => prefix4 9 p.1 * p.2)).sum.val = (prefix5 9 j).val := by decide +kernel
private lemma product_row_10 : ∀ j, ((factorColumns j).map (fun p => prefix4 10 p.1 * p.2)).sum.val = (prefix5 10 j).val := by decide +kernel
private lemma product_row_11 : ∀ j, ((factorColumns j).map (fun p => prefix4 11 p.1 * p.2)).sum.val = (prefix5 11 j).val := by decide +kernel
private lemma product_row_12 : ∀ j, ((factorColumns j).map (fun p => prefix4 12 p.1 * p.2)).sum.val = (prefix5 12 j).val := by decide +kernel
private lemma product_row_13 : ∀ j, ((factorColumns j).map (fun p => prefix4 13 p.1 * p.2)).sum.val = (prefix5 13 j).val := by decide +kernel
private lemma product_row_14 : ∀ j, ((factorColumns j).map (fun p => prefix4 14 p.1 * p.2)).sum.val = (prefix5 14 j).val := by decide +kernel
private lemma product_row_15 : ∀ j, ((factorColumns j).map (fun p => prefix4 15 p.1 * p.2)).sum.val = (prefix5 15 j).val := by decide +kernel
private lemma product_row_16 : ∀ j, ((factorColumns j).map (fun p => prefix4 16 p.1 * p.2)).sum.val = (prefix5 16 j).val := by decide +kernel
private lemma product_row_17 : ∀ j, ((factorColumns j).map (fun p => prefix4 17 p.1 * p.2)).sum.val = (prefix5 17 j).val := by decide +kernel
private lemma product_row_18 : ∀ j, ((factorColumns j).map (fun p => prefix4 18 p.1 * p.2)).sum.val = (prefix5 18 j).val := by decide +kernel
private lemma product_row_19 : ∀ j, ((factorColumns j).map (fun p => prefix4 19 p.1 * p.2)).sum.val = (prefix5 19 j).val := by decide +kernel
private lemma product_row_20 : ∀ j, ((factorColumns j).map (fun p => prefix4 20 p.1 * p.2)).sum.val = (prefix5 20 j).val := by decide +kernel
private lemma product_row_21 : ∀ j, ((factorColumns j).map (fun p => prefix4 21 p.1 * p.2)).sum.val = (prefix5 21 j).val := by decide +kernel
private lemma product_row_22 : ∀ j, ((factorColumns j).map (fun p => prefix4 22 p.1 * p.2)).sum.val = (prefix5 22 j).val := by decide +kernel
private lemma product_row_23 : ∀ j, ((factorColumns j).map (fun p => prefix4 23 p.1 * p.2)).sum.val = (prefix5 23 j).val := by decide +kernel
private lemma product_row_24 : ∀ j, ((factorColumns j).map (fun p => prefix4 24 p.1 * p.2)).sum.val = (prefix5 24 j).val := by decide +kernel
private lemma product_row_25 : ∀ j, ((factorColumns j).map (fun p => prefix4 25 p.1 * p.2)).sum.val = (prefix5 25 j).val := by decide +kernel
private lemma product_row_26 : ∀ j, ((factorColumns j).map (fun p => prefix4 26 p.1 * p.2)).sum.val = (prefix5 26 j).val := by decide +kernel
private lemma product_row_27 : ∀ j, ((factorColumns j).map (fun p => prefix4 27 p.1 * p.2)).sum.val = (prefix5 27 j).val := by decide +kernel
theorem prefix5_eq : prefix4 * curve 7 ⟨6⟩ = prefix5 := by
  apply mul_of_columns _ _ _ factorColumns factor_columns
  intro i j
  fin_cases i
  · exact product_row_0 j
  · exact product_row_1 j
  · exact product_row_2 j
  · exact product_row_3 j
  · exact product_row_4 j
  · exact product_row_5 j
  · exact product_row_6 j
  · exact product_row_7 j
  · exact product_row_8 j
  · exact product_row_9 j
  · exact product_row_10 j
  · exact product_row_11 j
  · exact product_row_12 j
  · exact product_row_13 j
  · exact product_row_14 j
  · exact product_row_15 j
  · exact product_row_16 j
  · exact product_row_17 j
  · exact product_row_18 j
  · exact product_row_19 j
  · exact product_row_20 j
  · exact product_row_21 j
  · exact product_row_22 j
  · exact product_row_23 j
  · exact product_row_24 j
  · exact product_row_25 j
  · exact product_row_26 j
  · exact product_row_27 j

end Triality.Standard.BinarySevenPlane.Certificate
