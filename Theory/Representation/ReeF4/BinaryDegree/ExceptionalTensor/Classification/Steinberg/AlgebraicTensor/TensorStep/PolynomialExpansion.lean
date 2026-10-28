module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Mathlib.Algebra.MvPolynomial.Equiv
/-!
# Polynomial expansions of rational root actions

Pull the regular matrix coefficients of a representing algebraic morphism
back along each actual root morphism. The affine line gives univariate
polynomials, whose finitely many coefficients assemble into endomorphisms.
This supplies root expansions from rationality without a polynomiality premise.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §5 and §11.
-/

public section

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]
variable {V : Type v} [AddCommGroup V] [Module F V]
private noncomputable def evalCoeffs (t : F) : (ℕ →₀ V) →ₗ[F] V :=
  Finsupp.lsum F (fun n => t ^ n • LinearMap.id)
omit [IsAlgClosed F] in
private lemma evalCoeffs_eq (t : F) (p : ℕ →₀ V) :
    evalCoeffs t p = p.sum (fun n v => t ^ n • v) := rfl
omit [IsAlgClosed F] in
private lemma evalCoeffs_scalar (t : F) (p : Polynomial F) (v : V) :
    evalCoeffs t (p.toFinsupp.coeff.mapRange (fun c => c • v) (zero_smul F v)) = p.eval t • v := by
  rw [evalCoeffs_eq, Finsupp.sum_mapRange_index (fun n => smul_zero (t ^ n))]
  simp only [Finsupp.sum, ← mul_smul, ← Finset.sum_smul, Polynomial.eval_eq_sum,
    Polynomial.sum, Polynomial.coeff, Polynomial.support, mul_comm]

private lemma root_matrix_polynomial [FiniteDimensional F V]
    (ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V)
    (hρ : IsRationalRepresentation ρ) :
    ∃ b : Module.Basis (Fin (Module.finrank F V)) F V,
      ∀ r i j, ∃ q : Polynomial F, ∀ t,
        q.eval t = b.repr ((ρ.action (algebraicRootElement r t)).val (b j)) i := by
  obtain ⟨b, f, hf⟩ := hρ
  refine ⟨b, ?_⟩
  intro r i j
  let c := Variety.PolynomialFunction.pullback (F4Chevalley.rootMorphism r).toVariety
    (rationalRepresentationMatrixCoefficient ρ b f i j)
  obtain ⟨q, hq⟩ := c.representedBy
  refine ⟨MvPolynomial.uniqueAlgEquiv F PUnit q, ?_⟩
  intro t
  rw [Polynomial.eval, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  have hc := hq (kPlusPoint t)
  change c (kPlusPoint t) = MvPolynomial.eval₂ (RingHom.id F) (fun _ => t) q at hc
  rw [← hc]
  exact rationalRepresentationMatrixCoefficient_apply ρ b f hf i j _

/-- Every finite-dimensional rational action has finite polynomial expansions
on the actual root subgroups. -/
theorem rootExpansion_nonempty [FiniteDimensional F V]
    (ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V)
    (hρ : IsRationalRepresentation ρ) : Nonempty (RootExpansion ρ) := by
  classical
  obtain ⟨b, hb⟩ := root_matrix_polynomial ρ hρ
  choose q hq using hb
  let E (i j : Fin (Module.finrank F V)) : Module.End F V := (b.coord j).smulRight (b i)
  let coeff (r : F4Chevalley.Root) : ℕ →₀ Module.End F V :=
    ∑ i, ∑ j, (q r i j).toFinsupp.coeff.mapRange (fun c => c • E i j) (zero_smul F _)
  refine ⟨⟨coeff, ?_⟩⟩
  intro r t
  change evalCoeffs t (coeff r) = _
  simp only [coeff, map_sum, evalCoeffs_scalar, hq]
  apply b.ext
  intro l
  simp [E, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Finsupp.single_apply, b.sum_repr]
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
