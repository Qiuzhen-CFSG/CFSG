module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.TargetData
/-!
# Matrix meaning of the normalization and target rows

The coordinate functionals restrict to the displayed 50-dimensional space,
and hence to linear forms in the 125 synthesis coefficients. Expanding the
products of these linear forms gives precisely the packed target rows. The
normalization row uses the proved identity x² = x in GF(2). The nine target
identities retain coordinate zero as a factor and require no normalization.

Source and ATLAS conventions: ../source/README.md and OrbitCover/Coordinates.
The intermediate coefficient calculations are certified in ChartData and
TargetData; the original saved calculations are preserved separately.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates MatrixChart

private theorem coordinates_restriction (S : RestrictionMatrix) (r : Fin 22) :
    coordinates (restrictionImage S) r =
      ∑ j : Fin 50, bit (restrictedChartRows.get r) j.val * S j 0 := by
  simp only [restrictionImage, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    coordinates, Matrix.dotProduct_mulVec]
  apply Finset.sum_congr rfl
  intro j _
  change (binaryColumn (dualRows.get r) ⬝ᵥ (fun i => restrictionEmbedding i j)) * S j 0 = _
  rw [← restrictedChartRows_spec]

private theorem coordinates_basis (a : Fin 125) (r : Fin 22) :
    coordinates (restrictionImage (restrictionLinearBasis a)) r =
      bit (chartRows.get r) a.val := by
  rw [coordinates_restriction, ← chartRows_spec]

private def chartLinear (r : Fin 22) (x : Coefficients) : ZMod 2 :=
  ∑ a, x a * bit (chartRows.get r) a.val

private theorem coordinates_linear (x : Coefficients) (r : Fin 22) :
    coordinates (restrictionImage (coefficientMatrix x)) r = chartLinear r x := by
  simp only [coordinates_coefficientMatrix, coordinates_basis, chartLinear]

private theorem product_expansion (r s : Fin 22) (x : Coefficients) :
    chartLinear r x * chartLinear s x =
      ∑ a, ∑ b, (bit (chartRows.get r) a.val * bit (chartRows.get s) b.val) *
        (x a * x b) := by
  simp only [chartLinear, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem list_expansion (ts : List (Fin 12 × Fin 12)) (x : Coefficients) :
    (ts.map (fun p => chartLinear (freeIndex p.1) x * chartLinear (freeIndex p.2) x)).sum =
      ∑ a, ∑ b, (ts.map (fun p => bit (chartRows.get (freeIndex p.1)) a.val *
        bit (chartRows.get (freeIndex p.2)) b.val)).sum * (x a * x b) := by
  induction ts with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [product_expansion, ih]
    simp only [add_mul, Finset.sum_add_distrib]

private theorem eval_diagonal (p : ℕ) (c : ZMod 2) (r : Fin 125 → ZMod 2)
    (hc : bit p 0 = c)
    (hr : ∀ a b : Fin 125, a ≤ b → bit p (slot a b) = if a = b then r a else 0)
    (x : Coefficients) : eval p x = (∑ a, x a * r a) + c := by
  rw [eval, hc, add_comm c]
  apply congrArg (· + c)
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · rw [if_pos (le_refl a), hr a a (le_refl a), if_pos rfl, square_eq_self]
    exact mul_comm _ _
  · intro b _ hba
    by_cases hab : a ≤ b
    · rw [if_pos hab, hr a b hab, if_neg (Ne.symm hba), zero_mul]
    · exact if_neg hab
  · simp

private theorem bit_select (m n a b : ℕ) :
    bit (if m.testBit a then n else 0) b = bit m a * bit n b := by
  cases h : m.testBit a <;> simp [bit, h]

private theorem targetBilinear_spec (k : Fin 9) (a b : Fin 125) :
    bit ((targetBilinearRows.get k).get a) b.val =
      bit (chartRows.get 0) a.val * bit (chartRows.get (quadraticIndex k)) b.val +
      ((quadraticTerms.get k).map (fun p =>
        bit (chartRows.get (freeIndex p.1)) a.val *
          bit (chartRows.get (freeIndex p.2)) b.val)).sum := by
  rw [targetBilinearRows_spec, bit_xor, bit_select, bit_xorList, List.map_map]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact bit_select _ _ _ _

theorem normalizationRow_eval (x : Coefficients) :
    eval normalizationRow x = coordinates (restrictionImage (coefficientMatrix x)) 0 + 1 := by
  rw [coordinates_linear]
  exact eval_diagonal normalizationRow 1 (fun a => bit (chartRows.get 0) a.val)
    (by decide +kernel) normalizationRow_coefficients x

theorem targetRows_eval (x : Coefficients) (k : Fin 9) :
    eval (targetRows.get k) x =
      coordinates (restrictionImage (coefficientMatrix x)) 0 *
        coordinates (restrictionImage (coefficientMatrix x)) (quadraticIndex k) +
      quadraticCoordinate k (freeCoordinates (restrictionImage (coefficientMatrix x))) := by
  have hc : ∀ k : Fin 9, bit (targetRows.get k) 0 = 0 := by decide +kernel
  rw [eval_of_coefficients (targetRows.get k) 0
    (fun a b => bit ((targetBilinearRows.get k).get a) b.val) (hc k)
    (targetRows_coefficients k)]
  simp only [zero_add, targetBilinear_spec, add_mul, Finset.sum_add_distrib,
    quadraticCoordinate, freeCoordinates, coordinates_linear]
  rw [← product_expansion, ← list_expansion]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
