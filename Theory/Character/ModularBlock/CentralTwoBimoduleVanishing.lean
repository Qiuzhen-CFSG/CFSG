module

public import Theory.Character.ModularBlock.BlockBimoduleTrace
public import Theory.Character.ModularBlock.MixedBrauerTrace
public import Theory.Representation.IntegralSpectralTrace

/-!
# Integral twisted bimodule traces at central two-elements

Let `e` be a central idempotent of the group algebra over the localization at
the chosen characteristic-two prime. If `z` is a nonidentity central element
of two-power order and `g,h` have odd order, the trace of left multiplication
by `z*g` and right multiplication by `h`, after projection by `e`, is zero
in the localization itself.

The odd-order left-right permutation has exponent the least common multiple
of the two element orders. This exponent is invertible and its roots of unity
lie in the coefficient ring. Integral spectral projectors reduce the claim
to the permutation-summand trace theorem for translation by `z`, which has
no fixed group-basis vectors. The row permutation convention uses inverses;
the actual bimodule operator uses right multiplication by `h`.

Source: the mixed Brauer--Suzuki trace argument cited by Fong, *Some Sylow
subgroups of order 32 and a characterization of U(3,3)*, J. Algebra 6 (1967),
p. 71, equation (6). This is the vanishing input for central two-quotients.
-/

public section

open scoped BigOperators
noncomputable section
namespace ModularBlock.BlockBimoduleTrace
open PrincipalBlockConstruction BrauerBlockReduction BrauerConjugationTrace MixedBrauerTrace
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Exact integral vanishing for a nonidentity central two-element and odd-order twists. -/
theorem integralTrace_centralTwo_twist_eq_zero
    (d : PrincipalCongruenceBlockData G)
    (e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (he : IsIdempotentElem e) (hec : e ∈ Set.center (MonoidAlgebra _ G))
    (z g h : G) (hzc : z ∈ Subgroup.center G) (hz : z ≠ 1)
    (hzpow : ∃ a : ℕ, z ^ (2 ^ a) = 1)
    (hg : Odd (orderOf g)) (hh : Odd (orderOf h)) :
    LinearMap.trace (Localization.AtPrime d.primeIdeal)
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
      (projectedBimultiplication e (z * g) h) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  let σ := leftRightPerm z 1
  let τ := leftRightPerm g h⁻¹
  let U := τ.permMatrix R
  let P := rightMatrix e
  let n := Nat.lcm (orderOf g) (orderOf h⁻¹)
  have hnodd : Nat.Coprime 2 n :=
    leftRight_lcm_coprime g h⁻¹ hg.coprime_two_left (by simpa using hh.coprime_two_left)
  have hn : n ≠ 0 := by
    intro hzero
    simp [hzero] at hnodd
  have hnunit : IsUnit (n : R) := isUnit_natCast_localization d n hnodd
  obtain ⟨ζ, hζ⟩ := exists_localization_primitiveRoot d n (leftRight_lcm_dvd_card g h⁻¹)
  obtain ⟨a, ha⟩ := hzpow
  have hσ : σ ^ (2 ^ a) = 1 :=
    leftRightPerm_pow_eq_one z 1 ha (one_pow _)
  have hfix : ∀ x, σ x ≠ x := by
    intro x hx
    have hinv : z⁻¹ = 1 := by
      apply mul_right_cancel (b := x)
      simpa [σ] using hx
    exact hz (inv_eq_one.mp hinv)
  have hU : U ^ n = 1 := by
    have hp : τ ^ n = 1 := leftRightPerm_lcm_pow_eq_one g h⁻¹
    have hm (m : ℕ) : U ^ m = (τ ^ m).permMatrix R := by
      induction m with
      | zero => simp [U]
      | succ m ih => rw [pow_succ', ih, pow_succ, Matrix.permMatrix_mul]
    rw [hm, hp, Matrix.permMatrix_one]
  have hTU : Commute (σ.permMatrix R) U := by
    change σ.permMatrix R * τ.permMatrix R = τ.permMatrix R * σ.permMatrix R
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
    congr 1
    ext x
    have hzg : Commute z g := (Subgroup.mem_center_iff.mp hzc g).symm
    simp only [σ, τ, Equiv.Perm.mul_apply, leftRightPerm_apply, mul_one]
    simp only [← mul_assoc]
    rw [hzg.inv_inv.eq]
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap _ R b, localizationToResidue_algebraMap d b⟩
  have hf (r : R) (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  have ht := Matrix.trace_permMatrix_mul_mul_eq_zero (localizationToResidue d)
    hsurj hf σ hσ hfix U P (rightMatrix_isIdempotent e he)
    (rightMatrix_commute_leftRight e hec z 1)
    (rightMatrix_commute_leftRight e hec g h⁻¹) hTU hn hU hnunit ζ hζ
  have htrace : Matrix.trace (σ.permMatrix R * U * P) =
      LinearMap.trace R (MonoidAlgebra R G) (projectedBimultiplication e (z * g) h) := by
    change Matrix.trace (σ.permMatrix R * τ.permMatrix R * rightMatrix e) = _
    rw [← Matrix.permMatrix_mul, PEquiv.toMatrix_toPEquiv_mul,
      trace_projectedBimultiplication]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, rightMatrix,
      Equiv.Perm.mul_apply, σ, τ, leftRightPerm_apply, mul_inv_rev,
      mul_one, id_eq, mul_assoc]
  exact htrace.symm.trans ht
end ModularBlock.BlockBimoduleTrace
