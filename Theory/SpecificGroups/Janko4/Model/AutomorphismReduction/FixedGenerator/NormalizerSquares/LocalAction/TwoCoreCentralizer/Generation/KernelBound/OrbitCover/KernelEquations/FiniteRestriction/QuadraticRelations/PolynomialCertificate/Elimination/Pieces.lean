module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Lookup

/-!
# Composition of bounded polynomial checks

A list of vanishing rows has vanishing XOR. This packages the soundness of
small numerical checks, so a long Gaussian witness can be checked in pieces.
The polynomial convention and Gaussian source are those of `../source/README.md`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
open Janko4.GeneratorCertificates

theorem eval_xorList_zero (ps : List ℕ) (x : Coefficients)
    (hs : List.Forall (fun p => eval p x = 0) ps) : eval (xorList ps) x = 0 := by
  induction ps with
  | nil => exact eval_zero x
  | cons p ps ih =>
    obtain ⟨hp, hs⟩ := (List.forall_cons _ _ _).mp hs
    rw [xorList, eval_xor, hp, ih hs, zero_add]

theorem eval_zero_of_pieces (ps : List ℕ) (target : ℕ)
    (hc : xorList ps = target) (x : Coefficients)
    (hs : List.Forall (fun p => eval p x = 0) ps) : eval target x = 0 := by
  rw [← hc]
  exact eval_xorList_zero ps x hs

theorem eval_product_zero_of_checked (a b : Affine) (r : ℕ)
    (hc : productRow a b = r) (x : Coefficients) (ha : eval (affineRow a) x = 0) :
    eval r x = 0 := by
  rw [← hc, eval_product, ha, zero_mul]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.Elimination
