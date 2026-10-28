module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Certificate.Prefix07

/-! The first 9 factors of the explicit Lang word on the full Geck lattice.
The sparse root-factor entries and every multiplication are kernel checked.
Source: the eleven-factor witness for the nonsplit torus at q = 2 (ATLAS p.89).
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane.Certificate
open Coefficients

def prefix8 : Matrix (Fin 28) (Fin 28) Scalar :=
  ![![⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨6⟩,⟨1⟩,⟨6⟩,⟨6⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨2⟩,⟨3⟩,⟨2⟩,⟨2⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨1⟩,⟨6⟩,⟨1⟩,⟨1⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨5⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨3⟩,⟨0⟩,⟨3⟩,⟨3⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨5⟩,⟨0⟩,⟨5⟩,⟨5⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨7⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨6⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨4⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨2⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨3⟩]]
private def factorColumns : Fin 28 → List (Fin 28 × Scalar) :=
  ![[(0,⟨1⟩),(11,⟨7⟩)],
    [(1,⟨1⟩),(11,⟨7⟩)],
    [(2,⟨1⟩),(11,⟨7⟩)],
    [(3,⟨1⟩),(11,⟨7⟩)],
    [(4,⟨1⟩),(17,⟨7⟩)],
    [(5,⟨1⟩),(19,⟨7⟩)],
    [(6,⟨1⟩)],
    [(7,⟨1⟩)],
    [(0,⟨7⟩),(1,⟨7⟩),(2,⟨7⟩),(3,⟨7⟩),(8,⟨1⟩),(11,⟨3⟩)],
    [(9,⟨1⟩)],
    [(10,⟨1⟩)],
    [(11,⟨1⟩)],
    [(12,⟨1⟩),(26,⟨7⟩)],
    [(13,⟨1⟩),(27,⟨7⟩)],
    [(14,⟨1⟩)],
    [(15,⟨1⟩)],
    [(6,⟨7⟩),(16,⟨1⟩)],
    [(17,⟨1⟩)],
    [(7,⟨7⟩),(18,⟨1⟩)],
    [(19,⟨1⟩)],
    [(20,⟨1⟩)],
    [(21,⟨1⟩)],
    [(22,⟨1⟩)],
    [(23,⟨1⟩)],
    [(14,⟨7⟩),(24,⟨1⟩)],
    [(15,⟨7⟩),(25,⟨1⟩)],
    [(26,⟨1⟩)],
    [(27,⟨1⟩)]]
private lemma factor_row_0 : ∀ j, (curve 7 ⟨7⟩ 0 j).val = (columnEntry (factorColumns j) 0).val := by decide +kernel
private lemma factor_row_1 : ∀ j, (curve 7 ⟨7⟩ 1 j).val = (columnEntry (factorColumns j) 1).val := by decide +kernel
private lemma factor_row_2 : ∀ j, (curve 7 ⟨7⟩ 2 j).val = (columnEntry (factorColumns j) 2).val := by decide +kernel
private lemma factor_row_3 : ∀ j, (curve 7 ⟨7⟩ 3 j).val = (columnEntry (factorColumns j) 3).val := by decide +kernel
private lemma factor_row_4 : ∀ j, (curve 7 ⟨7⟩ 4 j).val = (columnEntry (factorColumns j) 4).val := by decide +kernel
private lemma factor_row_5 : ∀ j, (curve 7 ⟨7⟩ 5 j).val = (columnEntry (factorColumns j) 5).val := by decide +kernel
private lemma factor_row_6 : ∀ j, (curve 7 ⟨7⟩ 6 j).val = (columnEntry (factorColumns j) 6).val := by decide +kernel
private lemma factor_row_7 : ∀ j, (curve 7 ⟨7⟩ 7 j).val = (columnEntry (factorColumns j) 7).val := by decide +kernel
private lemma factor_row_8 : ∀ j, (curve 7 ⟨7⟩ 8 j).val = (columnEntry (factorColumns j) 8).val := by decide +kernel
private lemma factor_row_9 : ∀ j, (curve 7 ⟨7⟩ 9 j).val = (columnEntry (factorColumns j) 9).val := by decide +kernel
private lemma factor_row_10 : ∀ j, (curve 7 ⟨7⟩ 10 j).val = (columnEntry (factorColumns j) 10).val := by decide +kernel
private lemma factor_row_11 : ∀ j, (curve 7 ⟨7⟩ 11 j).val = (columnEntry (factorColumns j) 11).val := by decide +kernel
private lemma factor_row_12 : ∀ j, (curve 7 ⟨7⟩ 12 j).val = (columnEntry (factorColumns j) 12).val := by decide +kernel
private lemma factor_row_13 : ∀ j, (curve 7 ⟨7⟩ 13 j).val = (columnEntry (factorColumns j) 13).val := by decide +kernel
private lemma factor_row_14 : ∀ j, (curve 7 ⟨7⟩ 14 j).val = (columnEntry (factorColumns j) 14).val := by decide +kernel
private lemma factor_row_15 : ∀ j, (curve 7 ⟨7⟩ 15 j).val = (columnEntry (factorColumns j) 15).val := by decide +kernel
private lemma factor_row_16 : ∀ j, (curve 7 ⟨7⟩ 16 j).val = (columnEntry (factorColumns j) 16).val := by decide +kernel
private lemma factor_row_17 : ∀ j, (curve 7 ⟨7⟩ 17 j).val = (columnEntry (factorColumns j) 17).val := by decide +kernel
private lemma factor_row_18 : ∀ j, (curve 7 ⟨7⟩ 18 j).val = (columnEntry (factorColumns j) 18).val := by decide +kernel
private lemma factor_row_19 : ∀ j, (curve 7 ⟨7⟩ 19 j).val = (columnEntry (factorColumns j) 19).val := by decide +kernel
private lemma factor_row_20 : ∀ j, (curve 7 ⟨7⟩ 20 j).val = (columnEntry (factorColumns j) 20).val := by decide +kernel
private lemma factor_row_21 : ∀ j, (curve 7 ⟨7⟩ 21 j).val = (columnEntry (factorColumns j) 21).val := by decide +kernel
private lemma factor_row_22 : ∀ j, (curve 7 ⟨7⟩ 22 j).val = (columnEntry (factorColumns j) 22).val := by decide +kernel
private lemma factor_row_23 : ∀ j, (curve 7 ⟨7⟩ 23 j).val = (columnEntry (factorColumns j) 23).val := by decide +kernel
private lemma factor_row_24 : ∀ j, (curve 7 ⟨7⟩ 24 j).val = (columnEntry (factorColumns j) 24).val := by decide +kernel
private lemma factor_row_25 : ∀ j, (curve 7 ⟨7⟩ 25 j).val = (columnEntry (factorColumns j) 25).val := by decide +kernel
private lemma factor_row_26 : ∀ j, (curve 7 ⟨7⟩ 26 j).val = (columnEntry (factorColumns j) 26).val := by decide +kernel
private lemma factor_row_27 : ∀ j, (curve 7 ⟨7⟩ 27 j).val = (columnEntry (factorColumns j) 27).val := by decide +kernel
private lemma factor_columns (i j) : curve 7 ⟨7⟩ i j = columnEntry (factorColumns j) i := by
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
private lemma product_row_0 : ∀ j, ((factorColumns j).map (fun p => prefix7 0 p.1 * p.2)).sum.val = (prefix8 0 j).val := by decide +kernel
private lemma product_row_1 : ∀ j, ((factorColumns j).map (fun p => prefix7 1 p.1 * p.2)).sum.val = (prefix8 1 j).val := by decide +kernel
private lemma product_row_2 : ∀ j, ((factorColumns j).map (fun p => prefix7 2 p.1 * p.2)).sum.val = (prefix8 2 j).val := by decide +kernel
private lemma product_row_3 : ∀ j, ((factorColumns j).map (fun p => prefix7 3 p.1 * p.2)).sum.val = (prefix8 3 j).val := by decide +kernel
private lemma product_row_4 : ∀ j, ((factorColumns j).map (fun p => prefix7 4 p.1 * p.2)).sum.val = (prefix8 4 j).val := by decide +kernel
private lemma product_row_5 : ∀ j, ((factorColumns j).map (fun p => prefix7 5 p.1 * p.2)).sum.val = (prefix8 5 j).val := by decide +kernel
private lemma product_row_6 : ∀ j, ((factorColumns j).map (fun p => prefix7 6 p.1 * p.2)).sum.val = (prefix8 6 j).val := by decide +kernel
private lemma product_row_7 : ∀ j, ((factorColumns j).map (fun p => prefix7 7 p.1 * p.2)).sum.val = (prefix8 7 j).val := by decide +kernel
private lemma product_row_8 : ∀ j, ((factorColumns j).map (fun p => prefix7 8 p.1 * p.2)).sum.val = (prefix8 8 j).val := by decide +kernel
private lemma product_row_9 : ∀ j, ((factorColumns j).map (fun p => prefix7 9 p.1 * p.2)).sum.val = (prefix8 9 j).val := by decide +kernel
private lemma product_row_10 : ∀ j, ((factorColumns j).map (fun p => prefix7 10 p.1 * p.2)).sum.val = (prefix8 10 j).val := by decide +kernel
private lemma product_row_11 : ∀ j, ((factorColumns j).map (fun p => prefix7 11 p.1 * p.2)).sum.val = (prefix8 11 j).val := by decide +kernel
private lemma product_row_12 : ∀ j, ((factorColumns j).map (fun p => prefix7 12 p.1 * p.2)).sum.val = (prefix8 12 j).val := by decide +kernel
private lemma product_row_13 : ∀ j, ((factorColumns j).map (fun p => prefix7 13 p.1 * p.2)).sum.val = (prefix8 13 j).val := by decide +kernel
private lemma product_row_14 : ∀ j, ((factorColumns j).map (fun p => prefix7 14 p.1 * p.2)).sum.val = (prefix8 14 j).val := by decide +kernel
private lemma product_row_15 : ∀ j, ((factorColumns j).map (fun p => prefix7 15 p.1 * p.2)).sum.val = (prefix8 15 j).val := by decide +kernel
private lemma product_row_16 : ∀ j, ((factorColumns j).map (fun p => prefix7 16 p.1 * p.2)).sum.val = (prefix8 16 j).val := by decide +kernel
private lemma product_row_17 : ∀ j, ((factorColumns j).map (fun p => prefix7 17 p.1 * p.2)).sum.val = (prefix8 17 j).val := by decide +kernel
private lemma product_row_18 : ∀ j, ((factorColumns j).map (fun p => prefix7 18 p.1 * p.2)).sum.val = (prefix8 18 j).val := by decide +kernel
private lemma product_row_19 : ∀ j, ((factorColumns j).map (fun p => prefix7 19 p.1 * p.2)).sum.val = (prefix8 19 j).val := by decide +kernel
private lemma product_row_20 : ∀ j, ((factorColumns j).map (fun p => prefix7 20 p.1 * p.2)).sum.val = (prefix8 20 j).val := by decide +kernel
private lemma product_row_21 : ∀ j, ((factorColumns j).map (fun p => prefix7 21 p.1 * p.2)).sum.val = (prefix8 21 j).val := by decide +kernel
private lemma product_row_22 : ∀ j, ((factorColumns j).map (fun p => prefix7 22 p.1 * p.2)).sum.val = (prefix8 22 j).val := by decide +kernel
private lemma product_row_23 : ∀ j, ((factorColumns j).map (fun p => prefix7 23 p.1 * p.2)).sum.val = (prefix8 23 j).val := by decide +kernel
private lemma product_row_24 : ∀ j, ((factorColumns j).map (fun p => prefix7 24 p.1 * p.2)).sum.val = (prefix8 24 j).val := by decide +kernel
private lemma product_row_25 : ∀ j, ((factorColumns j).map (fun p => prefix7 25 p.1 * p.2)).sum.val = (prefix8 25 j).val := by decide +kernel
private lemma product_row_26 : ∀ j, ((factorColumns j).map (fun p => prefix7 26 p.1 * p.2)).sum.val = (prefix8 26 j).val := by decide +kernel
private lemma product_row_27 : ∀ j, ((factorColumns j).map (fun p => prefix7 27 p.1 * p.2)).sum.val = (prefix8 27 j).val := by decide +kernel
theorem prefix8_eq : prefix7 * curve 7 ⟨7⟩ = prefix8 := by
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
