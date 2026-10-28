module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.PolynomialRegularity.MatrixReconstruction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.PolynomialRegularity.PresentedCoordinates
public import Theory.AlgebraicGroup.Variety.PolynomialFunction

/-!
# Polynomial regularity of the exceptional F4 point map

Assume restricted adjoint transport on the actual short ideal and the
exceptional root formula for a point endomorphism. The quotient-to-ideal
comparison reads its short columns from the input matrix. Applying the same
comparison to the inverse input gives the inverse short columns, which are
polynomial because inversion on the input carrier is regular. The short
operator detector then recovers all matrix entries using sums and products.

The literal general-linear presentation also has an auxiliary coordinate.
It is the determinant of the inverse point matrix, so it too is polynomial.
Thus the conclusion covers every coordinate of `F4Chevalley.Carrier` without
assuming a polynomial lift or an algebraic morphism realizing the point map.

This is the conditional regularity step in GLS3, Theorem 1.15.4(b)
(`refs/KGroup/GLS3/Chapter1.tex`), for Steinberg's exceptional root formula
(Theorem 28, `refs/KGroup/GLS3/Chapter2St1.tex`). Unconditional transport and
existence of the point endomorphism are separate inputs to final assembly.
-/

public section

open scoped Classical Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

private theorem constant_polynomial (c : F) :
    (fun _ : PointGroup F => c) ∈ (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring :=
  ⟨MvPolynomial.C c, fun x => by simp [evalPolynomial]⟩

private theorem polynomial_inv {f : PointGroup F → F}
    (hf : f ∈ (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring) :
    (fun x => f x⁻¹) ∈ (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨MvPolynomial.bind₁ AlgebraicGroup.invPolynomial p, ?_⟩
  intro x
  change f (x⁻¹) = _
  rw [hp, evalPolynomial_bind₁]
  congr 1
  funext i
  exact AlgebraicGroup.inv_regular i x

private theorem matrix_coordinate_polynomial (i j : Coordinate) :
    (fun x : PointGroup F => (pointMatrix x).val i j) ∈
      (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring := by
  refine ⟨MvPolynomial.X (Sum.inl
      (carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) i,
       carrierIndexEquiv (b := typeF4RootPairing_base) (k := F) j)), ?_⟩
  intro x
  simp only [pointMatrix_coordinate, evalPolynomial, MvPolynomial.eval₂_X]

omit [IsAlgClosed F] in
private theorem determinant_mem {X I : Type*} [Fintype I] [DecidableEq I]
    (R : Subring (X → F)) (hc : ∀ c : F, (fun _ : X => c) ∈ R)
    (A : X → Matrix I I F) (hA : ∀ i j, (fun x => A x i j) ∈ R) :
    (fun x => (A x).det) ∈ R := by
  have h : (∑ σ : Equiv.Perm I, (fun _ : X => (↑(Equiv.Perm.sign σ) : F)) *
      ∏ i : I, (fun x => A x (σ i) i)) ∈ R :=
    R.sum_mem fun σ _ => R.mul_mem (hc _) (R.prod_mem fun i _ => hA _ _)
  convert h using 1
  funext x
  simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]

variable [CharP F 2]

/-- Every entry of the actual matrix of the exceptional point map is polynomial
in the literal carrier coordinates. -/
theorem pointMatrix_exceptional_polynomial
    (htransport : HasShortAdjointTransport F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (i j : Coordinate) :
    ∃ p : MvPolynomial (F4Chevalley.Carrier (k := F)).Coordinates F,
      ∀ x : PointGroup F, (pointMatrix (ψ x)).val i j = evalPolynomial x.val p := by
  let R := (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring
  have hs (i j : Coordinate) (hj : IsShortCoordinate j) :
      (fun x : PointGroup F => (pointMatrix (ψ x)).val i j) ∈ R := by
    by_cases hi : IsShortCoordinate i
    · simpa only [pointMatrix_exceptional_short_column ψ hψ _ _ _ hj, if_pos hi] using
        matrix_coordinate_polynomial (F := F) (coordinatePermutation i) (coordinatePermutation j)
    · simpa only [pointMatrix_exceptional_short_column ψ hψ _ _ _ hj, if_neg hi] using (show (fun _ : PointGroup F => (0 : F)) ∈ R from R.zero_mem)
  have hi (i j : Coordinate) (hj : IsShortCoordinate j) :
      (fun x : PointGroup F => (pointMatrix (ψ x))⁻¹.val i j) ∈ R := by
    simpa only [map_inv] using polynomial_inv (hs i j hj)
  exact matrix_entries_mem_of_short htransport R constant_polynomial
    (fun x => pointMatrix (ψ x)) (fun x => pointMatrix_mem (ψ x)) hs hi i j

/-- Polynomial regularity on every coordinate of the literal F4 carrier,
including the auxiliary inverse-determinant coordinate. The only additional
premises are restricted adjoint transport and the specified exceptional root
formula on the given point endomorphism. -/
theorem exceptional_polynomial_regularity
    (htransport : HasShortAdjointTransport F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (i : (F4Chevalley.Carrier (k := F)).Coordinates) :
    ∃ p : MvPolynomial (F4Chevalley.Carrier (k := F)).Coordinates F,
      ∀ x : PointGroup F, (ψ x).val i = evalPolynomial x.val p := by
  rcases i with ⟨i, j⟩ | ⟨⟩
  · simpa only [point_coordinate_matrix] using
      pointMatrix_exceptional_polynomial htransport ψ hψ
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm i)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := F)).symm j)
  · have h := determinant_mem
      (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring constant_polynomial
      (fun x : PointGroup F => (pointMatrix (ψ x⁻¹)).val)
      (fun i j => polynomial_inv (pointMatrix_exceptional_polynomial htransport ψ hψ i j))
    change (fun x : PointGroup F => (ψ x).val (Sum.inr PUnit.unit)) ∈
      (F4Chevalley.Carrier (k := F)).polynomialFunctionSubring
    simpa only [point_auxiliary_coordinate, map_inv] using h

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
