module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Products
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Finite

/-!
# Annihilation of every quadratic term

The checked triangular products and functional values annihilate every
diagonal term. Symmetry of the test form turns a polarized term into pairing
with the weight plus its transpose. Interchanging the two operators covers
the reverse ordering, and linearity gives annihilation on the complete span.
The same calibration gives the stated evaluations on all 45 linear terms.

Source: the finite restriction calculation in KernelBound/source/README.md
and Separation/source/README.md.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

attribute [local irreducible] testForm squareBasis weights symWeights productWords productPairs

theorem linear_evaluation (k : Fin 44) (i : Fin 45) :
    functional (weights.get k.castSucc) (linearTerm testForm (squareBasis i)) =
      if i.val < 44 then (if i.val = k.val then 1 else 0) else bit survivor k.val := by
  rw [← linearWords_spec, functional_decode]
  exact linear_values k i

private theorem pairing_polar (w : ℕ) (D E : HalfMatrix) :
    functional w (polarTerm testForm D E) =
      pairing (decodeHalf w + (decodeHalf w)ᵀ) (Dᵀ * testForm * E) := by
  have ht : (Dᵀ * testForm * E)ᵀ = Eᵀ * testForm * D := by
    simp only [transpose_mul, transpose_transpose, testForm_transpose, Matrix.mul_assoc]
  have hp : pairing ((decodeHalf w)ᵀ) (Dᵀ * testForm * E) =
      pairing (decodeHalf w) (Eᵀ * testForm * D) := by
    rw [← ht, ← pairing_transpose (decodeHalf w) (Dᵀ * testForm * E)ᵀ, transpose_transpose]
  change pairing (decodeHalf w) (Dᵀ * testForm * E + Eᵀ * testForm * D) = _
  simp only [pairing, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at hp ⊢
  rw [hp]

theorem quadratic_annihilated (k : Fin 44) {R : HalfMatrix}
    (hR : R ∈ quadraticSpan testForm squareBasis) : functional (weights.get k.castSucc) R = 0 := by
  apply functional_quadratic_zero _ _ _ hR
  · intro i
    obtain ⟨p, hp⟩ := pair_coverage i i le_rfl
    have h := quadratic_values k p
    simp only [hp] at h
    rw [halfDot_spec, productWords_spec, hp] at h
    exact h
  · intro i j
    wlog hij : j ≤ i generalizing i j
    · have h := this j i (le_of_not_ge hij)
      simpa only [polarTerm, add_comm] using h
    by_cases he : i = j
    · subst j
      have hz : polarTerm testForm (squareBasis i) (squareBasis i) = 0 := by
        simp only [polarTerm, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [hz, map_zero]
    obtain ⟨p, hp⟩ := pair_coverage i j hij
    have h := quadratic_values k p
    simp only [hp, if_neg he] at h
    rw [halfDot_spec, symWeights_spec, productWords_spec, hp] at h
    rw [pairing_polar]
    exact h

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
