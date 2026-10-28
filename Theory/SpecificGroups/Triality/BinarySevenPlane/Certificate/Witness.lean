module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Certificate.Prefix10
public import Theory.SpecificGroups.Triality.BinarySevenPlane.Weyl

/-!
# The eleven-factor Lang matrix certificate

The canonical root matrices multiply to the displayed prefix matrix. Its
coefficient Frobenius is its product with the specified D₄ Weyl word. Every
entry is checked in the cubic coefficient ring, retaining all 28 coordinates.
The actual-field specialization is assembled in the Lang witness module.
Source: the explicit binary triality nonsplit-torus construction, ATLAS p.89.
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane.Certificate
open Coefficients PositiveCoordinates.SumExchangeData ConcreteBruhat.MatrixRealization

def curveWord : Matrix (Fin 28) (Fin 28) Scalar :=
  curve 14 ⟨2⟩ * curve 3 ⟨4⟩ * curve 4 ⟨1⟩ * curve 7 ⟨1⟩ *
  curve 4 ⟨2⟩ * curve 7 ⟨6⟩ * curve 4 ⟨3⟩ * curve 13 ⟨1⟩ *
  curve 7 ⟨7⟩ * curve 0 ⟨6⟩ * curve 4 ⟨7⟩

theorem curveWord_eq : curveWord = prefix10 := by
  simp only [curveWord, prefix0_eq, prefix1_eq, prefix2_eq, prefix3_eq,
    prefix4_eq, prefix5_eq, prefix6_eq, prefix7_eq, prefix8_eq, prefix9_eq, prefix10_eq]

def wordCoefficient (l : List (Fin 4)) : Matrix Index Index Scalar :=
  fun a b => match b with
    | .inl j => corootVector Scalar (permWord l (simpleIndex j)) a
    | .inr r => if a = .inr (permWord l r) then 1 else 0

def weylMatrix : Matrix (Fin 28) (Fin 28) Scalar :=
  ![![⟨0⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨1⟩,⟨1⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨1⟩,⟨1⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩],
    ![⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨1⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩]]
private lemma weyl_row_0 : ∀ j, (weylMatrix 0 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 0) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_1 : ∀ j, (weylMatrix 1 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 1) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_2 : ∀ j, (weylMatrix 2 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 2) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_3 : ∀ j, (weylMatrix 3 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 3) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_4 : ∀ j, (weylMatrix 4 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 4) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_5 : ∀ j, (weylMatrix 5 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 5) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_6 : ∀ j, (weylMatrix 6 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 6) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_7 : ∀ j, (weylMatrix 7 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 7) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_8 : ∀ j, (weylMatrix 8 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 8) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_9 : ∀ j, (weylMatrix 9 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 9) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_10 : ∀ j, (weylMatrix 10 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 10) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_11 : ∀ j, (weylMatrix 11 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 11) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_12 : ∀ j, (weylMatrix 12 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 12) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_13 : ∀ j, (weylMatrix 13 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 13) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_14 : ∀ j, (weylMatrix 14 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 14) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_15 : ∀ j, (weylMatrix 15 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 15) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_16 : ∀ j, (weylMatrix 16 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 16) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_17 : ∀ j, (weylMatrix 17 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 17) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_18 : ∀ j, (weylMatrix 18 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 18) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_19 : ∀ j, (weylMatrix 19 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 19) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_20 : ∀ j, (weylMatrix 20 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 20) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_21 : ∀ j, (weylMatrix 21 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 21) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_22 : ∀ j, (weylMatrix 22 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 22) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_23 : ∀ j, (weylMatrix 23 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 23) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_24 : ∀ j, (weylMatrix 24 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 24) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_25 : ∀ j, (weylMatrix 25 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 25) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_26 : ∀ j, (weylMatrix 26 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 26) (finSumFinEquiv.symm j)).val := by decide +kernel
private lemma weyl_row_27 : ∀ j, (weylMatrix 27 j).val = (wordCoefficient [1,0,2,3,1,0,2,3] (finSumFinEquiv.symm 27) (finSumFinEquiv.symm j)).val := by decide +kernel
theorem weylMatrix_eq : weylMatrix = Matrix.reindexRingEquiv Scalar finSumFinEquiv
    (wordCoefficient [1,0,2,3,1,0,2,3]) := by
  ext i j
  apply congrArg Scalar.mk
  fin_cases i
  · exact weyl_row_0 j
  · exact weyl_row_1 j
  · exact weyl_row_2 j
  · exact weyl_row_3 j
  · exact weyl_row_4 j
  · exact weyl_row_5 j
  · exact weyl_row_6 j
  · exact weyl_row_7 j
  · exact weyl_row_8 j
  · exact weyl_row_9 j
  · exact weyl_row_10 j
  · exact weyl_row_11 j
  · exact weyl_row_12 j
  · exact weyl_row_13 j
  · exact weyl_row_14 j
  · exact weyl_row_15 j
  · exact weyl_row_16 j
  · exact weyl_row_17 j
  · exact weyl_row_18 j
  · exact weyl_row_19 j
  · exact weyl_row_20 j
  · exact weyl_row_21 j
  · exact weyl_row_22 j
  · exact weyl_row_23 j
  · exact weyl_row_24 j
  · exact weyl_row_25 j
  · exact weyl_row_26 j
  · exact weyl_row_27 j
private def weylColumns : Fin 28 → List (Fin 28 × Scalar) :=
  ![[(1,⟨1⟩),(2,⟨1⟩),(3,⟨1⟩)],
    [(0,⟨1⟩),(1,⟨1⟩),(2,⟨1⟩),(3,⟨1⟩)],
    [(0,⟨1⟩),(1,⟨1⟩),(3,⟨1⟩)],
    [(0,⟨1⟩),(1,⟨1⟩),(2,⟨1⟩)],
    [(18,⟨1⟩)],
    [(19,⟨1⟩)],
    [(16,⟨1⟩)],
    [(17,⟨1⟩)],
    [(7,⟨1⟩)],
    [(5,⟨1⟩)],
    [(6,⟨1⟩)],
    [(4,⟨1⟩)],
    [(22,⟨1⟩)],
    [(23,⟨1⟩)],
    [(20,⟨1⟩)],
    [(21,⟨1⟩)],
    [(10,⟨1⟩)],
    [(8,⟨1⟩)],
    [(11,⟨1⟩)],
    [(9,⟨1⟩)],
    [(24,⟨1⟩)],
    [(25,⟨1⟩)],
    [(26,⟨1⟩)],
    [(27,⟨1⟩)],
    [(14,⟨1⟩)],
    [(15,⟨1⟩)],
    [(12,⟨1⟩)],
    [(13,⟨1⟩)]]
private lemma weyl_columns (i j) : weylMatrix i j = columnEntry (weylColumns j) i := by
  apply congrArg Scalar.mk
  revert i j
  decide +kernel
private lemma frobenius_row_0 : ∀ j, ((weylColumns j).map (fun p => prefix10 0 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 0 j).val := by decide +kernel
private lemma frobenius_row_1 : ∀ j, ((weylColumns j).map (fun p => prefix10 1 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 1 j).val := by decide +kernel
private lemma frobenius_row_2 : ∀ j, ((weylColumns j).map (fun p => prefix10 2 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 2 j).val := by decide +kernel
private lemma frobenius_row_3 : ∀ j, ((weylColumns j).map (fun p => prefix10 3 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 3 j).val := by decide +kernel
private lemma frobenius_row_4 : ∀ j, ((weylColumns j).map (fun p => prefix10 4 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 4 j).val := by decide +kernel
private lemma frobenius_row_5 : ∀ j, ((weylColumns j).map (fun p => prefix10 5 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 5 j).val := by decide +kernel
private lemma frobenius_row_6 : ∀ j, ((weylColumns j).map (fun p => prefix10 6 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 6 j).val := by decide +kernel
private lemma frobenius_row_7 : ∀ j, ((weylColumns j).map (fun p => prefix10 7 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 7 j).val := by decide +kernel
private lemma frobenius_row_8 : ∀ j, ((weylColumns j).map (fun p => prefix10 8 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 8 j).val := by decide +kernel
private lemma frobenius_row_9 : ∀ j, ((weylColumns j).map (fun p => prefix10 9 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 9 j).val := by decide +kernel
private lemma frobenius_row_10 : ∀ j, ((weylColumns j).map (fun p => prefix10 10 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 10 j).val := by decide +kernel
private lemma frobenius_row_11 : ∀ j, ((weylColumns j).map (fun p => prefix10 11 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 11 j).val := by decide +kernel
private lemma frobenius_row_12 : ∀ j, ((weylColumns j).map (fun p => prefix10 12 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 12 j).val := by decide +kernel
private lemma frobenius_row_13 : ∀ j, ((weylColumns j).map (fun p => prefix10 13 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 13 j).val := by decide +kernel
private lemma frobenius_row_14 : ∀ j, ((weylColumns j).map (fun p => prefix10 14 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 14 j).val := by decide +kernel
private lemma frobenius_row_15 : ∀ j, ((weylColumns j).map (fun p => prefix10 15 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 15 j).val := by decide +kernel
private lemma frobenius_row_16 : ∀ j, ((weylColumns j).map (fun p => prefix10 16 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 16 j).val := by decide +kernel
private lemma frobenius_row_17 : ∀ j, ((weylColumns j).map (fun p => prefix10 17 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 17 j).val := by decide +kernel
private lemma frobenius_row_18 : ∀ j, ((weylColumns j).map (fun p => prefix10 18 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 18 j).val := by decide +kernel
private lemma frobenius_row_19 : ∀ j, ((weylColumns j).map (fun p => prefix10 19 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 19 j).val := by decide +kernel
private lemma frobenius_row_20 : ∀ j, ((weylColumns j).map (fun p => prefix10 20 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 20 j).val := by decide +kernel
private lemma frobenius_row_21 : ∀ j, ((weylColumns j).map (fun p => prefix10 21 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 21 j).val := by decide +kernel
private lemma frobenius_row_22 : ∀ j, ((weylColumns j).map (fun p => prefix10 22 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 22 j).val := by decide +kernel
private lemma frobenius_row_23 : ∀ j, ((weylColumns j).map (fun p => prefix10 23 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 23 j).val := by decide +kernel
private lemma frobenius_row_24 : ∀ j, ((weylColumns j).map (fun p => prefix10 24 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 24 j).val := by decide +kernel
private lemma frobenius_row_25 : ∀ j, ((weylColumns j).map (fun p => prefix10 25 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 25 j).val := by decide +kernel
private lemma frobenius_row_26 : ∀ j, ((weylColumns j).map (fun p => prefix10 26 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 26 j).val := by decide +kernel
private lemma frobenius_row_27 : ∀ j, ((weylColumns j).map (fun p => prefix10 27 p.1 * p.2)).sum.val = ((frobenius Scalar 2).mapMatrix prefix10 27 j).val := by decide +kernel
theorem frobenius_curveWord : (frobenius Scalar 2).mapMatrix curveWord =
    curveWord * weylMatrix := by
  rw [curveWord_eq]
  symm
  apply mul_of_columns _ _ _ weylColumns weyl_columns
  intro i j
  fin_cases i
  · exact frobenius_row_0 j
  · exact frobenius_row_1 j
  · exact frobenius_row_2 j
  · exact frobenius_row_3 j
  · exact frobenius_row_4 j
  · exact frobenius_row_5 j
  · exact frobenius_row_6 j
  · exact frobenius_row_7 j
  · exact frobenius_row_8 j
  · exact frobenius_row_9 j
  · exact frobenius_row_10 j
  · exact frobenius_row_11 j
  · exact frobenius_row_12 j
  · exact frobenius_row_13 j
  · exact frobenius_row_14 j
  · exact frobenius_row_15 j
  · exact frobenius_row_16 j
  · exact frobenius_row_17 j
  · exact frobenius_row_18 j
  · exact frobenius_row_19 j
  · exact frobenius_row_20 j
  · exact frobenius_row_21 j
  · exact frobenius_row_22 j
  · exact frobenius_row_23 j
  · exact frobenius_row_24 j
  · exact frobenius_row_25 j
  · exact frobenius_row_26 j
  · exact frobenius_row_27 j

end Triality.Standard.BinarySevenPlane.Certificate
