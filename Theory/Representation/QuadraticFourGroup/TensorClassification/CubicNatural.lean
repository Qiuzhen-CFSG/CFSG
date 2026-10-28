module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.AlgebraicInputs
public import Theory.Representation.QuadraticFourGroup.TensorClassification.SchurReduction
public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison
public import Theory.Representation.Quotient
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Cubic-fixed-point-free irreducible PSL₂ modules

Over an algebraically closed field of characteristic two, an irreducible
representation of `PSL₂(2^n)` on which every order-three element acts without
nonzero fixed vectors is an actual Frobenius twist of the natural module.
The conclusion uses the specified coefficient embedding and natural matrices.

Pull back through the characteristic-two isomorphism `SL₂ ≃ PSL₂` and apply
the classification by restricted highest-weight orbit spans. The companion
matrix of `X² + X + 1` cycles `X₀`, `X₁`, and `X₀ + X₁`. Thus the orbit sum
`X₀^m + X₁^m + (X₀ + X₁)^m` belongs to the degree-`m` highest-weight span and
is fixed. It is nonzero at weight zero. At positive weight, its vanishing
forces all intermediate binomial coefficients to be even; Lucas's theorem
then forces `m` to be a power of two. This argument works for both split and
nonsplit cubic elements. The explicit pure-power intertwiner identifies the
remaining span with the Frobenius natural module, and inflation descends the
intertwiner to the genuine projective group.

Source: GLS2, Theorem 25.14, Step 5, `refs/KGroup/GLS2/ChapterG.tex`,
lines 906--928. The Schur-closure specialization discharges the single-factor
classification input of the natural-tensor descent.
-/

public section

open scoped MatrixGroups
open MvPolynomial
open Representation.SL2
namespace Representation.QuadraticFourGroup.TensorClassification

variable {K F : Type*} [Field K] [Field F] [CharP F 2]

private theorem eq_two_pow_of_orbit_sum_eq_zero (m : ℕ)
    (h : (X 0 ^ m + X 1 ^ m + (X 0 + X 1) ^ m : MvPolynomial (Fin 2) F) = 0) :
    ∃ i : ℕ, m = 2 ^ i := by
  have hm : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    subst m
    simp [CharTwo.add_self_eq_zero] at h
  have hp : (Polynomial.X ^ m + 1 + (Polynomial.X + 1) ^ m : Polynomial F) = 0 := by
    simpa using congrArg (MvPolynomial.aeval (![Polynomial.X, 1] : Fin 2 → Polynomial F)) h
  refine ⟨multiplicity 2 m, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hm ?_⟩
  intro r hr
  have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
  have hrm : r ≠ m := by have := (Finset.mem_Icc.mp hr).2; omega
  have hc := congrArg (fun q : Polynomial F => q.coeff r) hp
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hrm,
    Polynomial.coeff_one, if_neg hr0, Polynomial.coeff_X_add_one_pow,
    zero_add, Polynomial.coeff_zero] at hc
  exact Nat.modEq_zero_iff_dvd.mpr ((CharP.cast_eq_zero_iff F 2 _).mp hc)

omit [CharP F 2] in
private theorem cubicAction_X_zero (e : K →+* F) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K)) (X 0) =
      (X 1 : MvPolynomial (Fin 2) F) := by
  simp only [polynomialAction, MvPolynomial.aeval_X, Fin.sum_univ_two]
  change C (e 0) * X 0 + C (e 1) * X 1 = _
  simp

private theorem cubicAction_X_one (e : K →+* F) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K)) (X 1) =
      (X 0 + X 1 : MvPolynomial (Fin 2) F) := by
  simp only [polynomialAction, MvPolynomial.aeval_X, Fin.sum_univ_two]
  change C (e (-1)) * X 0 + C (e (-1)) * X 1 = _
  simp [CharTwo.neg_eq]

private theorem cubicAction_X_add (e : K →+* F) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K)) (X 0 + X 1) =
      (X 0 : MvPolynomial (Fin 2) F) := by
  rw [map_add, cubicAction_X_zero, cubicAction_X_one]
  simp [CharTwo.add_self_eq_zero, add_left_comm]

/-- The explicit cubic orbit sum gives a nonzero fixed vector for every
highest weight other than a single binary power, including weight zero. -/
theorem exists_nonzero_cubic_fixed_highestWeight (e : K →+* F) (m : ℕ)
    (hm : ∀ i : ℕ, m ≠ 2 ^ i) :
    ∃ f : (highestWeightSpan e m).toSubmodule, f ≠ 0 ∧
      (highestWeightSpan e m).toRepresentation (cubicMatrix K) f = f := by
  let P : MvPolynomial (Fin 2) F := X 0 ^ m + X 1 ^ m + (X 0 + X 1) ^ m
  have h0 := X_pow_mem_highestWeightSpan e m
  have h1 : (X 1 : MvPolynomial (Fin 2) F) ^ m ∈ highestWeightSpan e m := by
    have h := (highestWeightSpan e m).apply_mem_toSubmodule (cubicMatrix K) h0
    change polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K))
      (X 0 ^ m) ∈ _ at h
    rwa [map_pow, cubicAction_X_zero] at h
  have h01 : (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ m ∈ highestWeightSpan e m := by
    have h := (highestWeightSpan e m).apply_mem_toSubmodule (cubicMatrix K) h1
    change polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K))
      (X 1 ^ m) ∈ _ at h
    rwa [map_pow, cubicAction_X_one] at h
  have hP : P ∈ highestWeightSpan e m :=
    (highestWeightSpan e m).toSubmodule.add_mem
      ((highestWeightSpan e m).toSubmodule.add_mem h0 h1) h01
  refine ⟨⟨P, hP⟩, ?_, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := eq_two_pow_of_orbit_sum_eq_zero (F := F) m (congrArg Subtype.val h)
    exact hm i hi
  · apply Subtype.ext
    change polynomialAction F (Matrix.SpecialLinearGroup.map e (cubicMatrix K)) P = P
    dsimp only [P]
    rw [map_add, map_add, map_pow, map_pow, map_pow,
      cubicAction_X_zero, cubicAction_X_one, cubicAction_X_add]
    abel

/-- A cubic-fixed-point-free highest-weight orbit span has a single binary digit. -/
theorem highestWeight_eq_two_pow_of_cubic_fixedPointFree (e : K →+* F) (m : ℕ)
    (h : FixedPointFreeAt (highestWeightSpan e m).toRepresentation (cubicMatrix K)) :
    ∃ i : ℕ, m = 2 ^ i := by
  by_contra! hm
  obtain ⟨f, hf, hfix⟩ := exists_nonzero_cubic_fixed_highestWeight e m hm
  exact hf (h f hfix)

omit [CharP F 2] in
private theorem naturalAction_comp_specialLinearEquiv {n : ℕ} (e : GaloisField 2 n →+* F) :
    (naturalAction e).comp (specialLinearEquivFactor n).toMonoidHom =
      BinarySmall.embeddedNatural e := by
  ext g : 1
  apply LinearMap.ext
  intro v
  ext j
  change Matrix.mulVec
    ((Matrix.SpecialLinearGroup.map e) ((specialLinearEquivFactor n).symm
      ((specialLinearEquivFactor n) g))).val v j =
    Matrix.mulVec ((Matrix.SpecialLinearGroup.map e) g).val v j
  rw [MulEquiv.symm_apply_apply]

private theorem mappedFrobeniusNatural_comp_specialLinearEquiv {n : ℕ}
    (e : GaloisField 2 n →+* F) (i : ℕ) :
    (mappedFrobeniusNatural e i).comp (specialLinearEquivFactor n).toMonoidHom =
      BinarySmall.embeddedNatural ((iterateFrobenius F 2 i).comp e) := by
  rw [mappedFrobeniusNatural, naturalAction_comp_specialLinearEquiv]
  congr 1
  ext a
  simp [iterateFrobenius_def]

/-- Testing the specified order-three element already identifies an irreducible
module with an actual Frobenius natural action on the projective group. -/
theorem exists_mappedFrobeniusNatural_equiv_of_cubic_fixedPointFree
    {n : ℕ} (hn : 1 < n) [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : GaloisField 2 n →+* F) (τ : Representation F (Factor n) V)
    [τ.IsIrreducible] (h : FixedPointFreeAt τ (cubicElement n)) :
    ∃ i : ℕ, i < n ∧ Nonempty (τ.Equiv (mappedFrobeniusNatural e i)) := by
  let ρ : Representation F SL(2, GaloisField 2 n) V := τ.comp (specialLinearEquivFactor n).toMonoidHom
  let : ρ.IsIrreducible := (irreducible_comp_surjective_iff
    (specialLinearEquivFactor n).toMonoidHom (specialLinearEquivFactor n).surjective τ).mpr
      inferInstance
  obtain ⟨m, ⟨ψ⟩⟩ := exists_highestWeightSpan_equiv e 2 ρ
  have hρ : FixedPointFreeAt ρ (cubicMatrix (GaloisField 2 n)) := h
  obtain ⟨i, hi⟩ := highestWeight_eq_two_pow_of_cubic_fixedPointFree e m (hρ.of_equiv ψ)
  have hin : i < n := by
    have hm := m.isLt
    rw [hi, GaloisField.card 2 n (by omega)] at hm
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hm
  rw [hi] at ψ
  have η := ψ.trans (BinarySmall.highestWeightPurePowerEquiv e i)
  refine ⟨i, hin, ⟨inflationEquiv (specialLinearEquivFactor n).toMonoidHom
    (specialLinearEquivFactor n).surjective τ (mappedFrobeniusNatural e i) ?_⟩⟩
  rw [mappedFrobeniusNatural_comp_specialLinearEquiv]
  exact η

/-- The single-factor classification required by GLS2 Theorem 25.14, Step 5. -/
theorem cubicNaturalClassification {n : ℕ} (hn : 1 < n) [IsAlgClosed F]
    (e : GaloisField 2 n →+* F) : CubicNaturalClassification e := by
  intro d τ hirr h
  let := hirr
  exact exists_mappedFrobeniusNatural_equiv_of_cubic_fixedPointFree hn e τ
    (h (cubicElement n) (cubicElement_order n))

/-- Apply the classification over the actual Schur closure of the binary module.
This supplies the `CubicNaturalClassification` premise of tensor descent. -/
theorem cubicNaturalClassification_schurClosure {n : ℕ} (hn : 1 < n)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible] :
    CubicNaturalClassification (schurClosureEmbedding σ) :=
  cubicNaturalClassification hn (schurClosureEmbedding σ)

end Representation.QuadraticFourGroup.TensorClassification

end
