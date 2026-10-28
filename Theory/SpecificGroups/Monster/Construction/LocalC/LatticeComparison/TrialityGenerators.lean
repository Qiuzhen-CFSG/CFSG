module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.TrialityGenerators.Basic
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.TrialityGenerators.Relations
/-!
# Triality conjugation in the source Golay–Leech coordinates

The action is the actual conjugation `g * q * g⁻¹` on `Q1`, restricted by its
normality in `N1`. The first loop-generator family acts trivially on the
abelian coordinate quotient. For the second family, the Parker collection
identities give the sign formula, including its parity-dependent code and
cocode corrections. A standard automorphism induces its genuine coordinate
permutation on both factors; its odd case interchanges the second and third
sign generators, which have the same quotient coordinates.

Every calculation is made on the normal form
`psiAut1N (parkerCocodeStandard c) * psi2N (0,t) * psi1N d` and then extended
to every element of `Q1` by the proved parametrization. The additions used
when collecting its three factors are the twisted additions of Exercise 4.6.
No lattice isometry or transported lattice action enters these proofs.

Source: Aschbacher, *Sporadic Groups*, Section 14 and Exercise 4.6(4),
printed pp. 58–64; Lemma 27.2, pp. 144–145; generator comparison, p. 148.
Lean function composition reverses the source's right-action products:
source conjugation by `g` therefore becomes `g * q * g⁻¹` here.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer
namespace Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation
open TrialitySpin

private def first (d : ParkerLoop) : Q1 := q1Param (d,0,0)
private def sign (t : ParkerBit) : Q1 := q1Param ((0,0),t,0)
private def cocode (c : Cocode) : Q1 := q1Param ((0,0),0,c)
private def third (t : ParkerBit) : Q1 := first (0,t) * sign t

private theorem first_val (d : ParkerLoop) : (first d).val = psi1N d := by
  change (q1Word d 0 0).val = _
  rw [q1Word_cocode_zero]
  change psi2N loopOne * psi1N d = _
  rw [psi2_one, one_mul]

private theorem sign_val (t : ParkerBit) : (sign t).val = psi2N (0,t) := by
  change (q1Word (0,0) t 0).val = _
  rw [q1Word_cocode_zero]
  change psi2N (0,t) * psi1N loopOne = _
  rw [psi1_one, mul_one]

private theorem cocode_val (c : Cocode) : (cocode c).val = psiAut1N (parkerCocodeStandard c) := by
  change psiAut1N (parkerCocodeStandard c) * psi2N loopOne * psi1N loopOne = _
  rw [psi2_one, psi1_one, mul_one, mul_one]

private theorem third_val (t : ParkerBit) : (third t).val = psi3N (0,t) := by
  change (first (0,t)).val * (sign t).val = _
  rw [first_val, sign_val]
  have ht : t = 0 ∨ t = 1 := by revert t; decide
  rcases ht with rfl | rfl
  · change psi1N loopOne * psi2N loopOne = psi3N loopOne
    rw [psi1_one, psi2_one, mul_one]
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change (a,b,c) = psi3 loopOne (a,b,c)
    simp
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change z1 (z2 (a,b,c)) = z3 (a,b,c)
    simp

private def coordinates (q : Q1) : QuadraticCoordinates := (q1Coordinates q).toAdd

@[simp] private theorem coordinates_mul (q r : Q1) :
    coordinates (q * r) = coordinates q + coordinates r := by
  exact congrArg Multiplicative.toAdd (q1Coordinates.map_mul q r)

@[simp] private theorem first_coordinates (d : ParkerLoop) : coordinates (first d) = ⟨d.1,0⟩ := by
  simp [coordinates, first, q1WordCoordinates]

@[simp] private theorem sign_coordinates (t : ParkerBit) : coordinates (sign t) = ⟨t • golayOne,0⟩ := by
  simp [coordinates, sign, q1WordCoordinates]

@[simp] private theorem cocode_coordinates (c : Cocode) : coordinates (cocode c) = ⟨0,c⟩ := by
  simp [coordinates, cocode, q1WordCoordinates]

@[simp] private theorem third_coordinates (t : ParkerBit) :
    coordinates (third t) = ⟨t • golayOne,0⟩ := by
  simp [third, quadraticCoordinates_add_eq, coordinateSum]

private theorem param_eq (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    q1Param (d,t,c) = cocode c * sign t * first d := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, first_val, sign_val, cocode_val]
  rfl

private theorem cocode_even_iff (c : Cocode) :
    (parkerCocodeStandard c).val parkerOmega = parkerOmega ↔ cocodeParity c = 0 := by
  simp [parkerOmega, cocodePairing_one]

private theorem cocode_apply (c : Cocode) (d : ParkerLoop) :
    (parkerCocodeStandard c).val d = parkerSign (cocodePairing d.1 c) d := rfl

end Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation

namespace Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation
open TrialitySpin

private def signConjugation (d : ParkerLoop) : MulAut Q1 :=
  q1Conjugation ⟨psi2N d, psi2N_mem_N1 d⟩

private theorem signConjugation_first (d e : ParkerLoop) :
    signConjugation e (first d) =
      cocode (intersectionCocode e.1 d.1) * third (golayHalfOverlap e.1 d.1) * first d := by
  apply Subtype.ext
  simp only [signConjugation, q1Conjugation_val, first_val, Subgroup.coe_mul,
    cocode_val, third_val]
  exact psi2N_conj_psi1N d e

private theorem signConjugation_sign (d : ParkerLoop) (t : ParkerBit) :
    signConjugation d (sign t) = sign t := by
  have ht : t = 0 ∨ t = 1 := by revert t; decide
  have hc : Commute (psi2N d) (psi2N (0,t)) := by
    rcases ht with rfl | rfl
    · change Commute (psi2N d) (psi2N loopOne)
      rw [psi2_one]; exact Commute.one_right _
    · apply Subtype.ext
      ext ⟨a,b,c⟩ : 1
      change psi2 d (z2 (a,b,c)) = z2 (psi2 d (a,b,c))
      simp
  apply Subtype.ext
  simp only [signConjugation, q1Conjugation_val, sign_val]
  rw [hc.eq, mul_inv_cancel_right]

private theorem cocode_symm (c : Cocode) (d : ParkerLoop) :
    (parkerCocodeStandard c).val.symm d = (parkerCocodeStandard c).val d := by
  apply (parkerCocodeStandard c).val.injective
  simp [parkerCocodeStandard_apply, add_assoc]

private theorem signConjugation_cocode_even (d : ParkerLoop) (c : Cocode)
    (hc : cocodeParity c = 0) :
    signConjugation d (cocode c) = cocode c * sign (cocodePairing d.1 c) := by
  have hm := aut_psi2_even (parkerCocodeStandard c) ((cocode_even_iff c).mpr hc)
    ((parkerCocodeStandard c).val.symm d)
  rw [Equiv.apply_symm_apply] at hm
  simp only [cocode_symm, cocode_apply, psi2_sign] at hm
  apply Subtype.ext
  simp only [signConjugation, q1Conjugation_val, Subgroup.coe_mul, cocode_val, sign_val]
  rw [← hm]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

private theorem signConjugation_cocode_odd (d : ParkerLoop) (c : Cocode)
    (hc : cocodeParity c ≠ 0) :
    signConjugation d (cocode c) =
      cocode c * third (cocodePairing d.1 c) * first d := by
  have hm := aut_psi3_odd (parkerCocodeStandard c) ((cocode_even_iff c).not.mpr hc)
    (loopInverse ((parkerCocodeStandard c).val.symm d))
  rw [loopInverse_inverse, Equiv.apply_symm_apply] at hm
  simp only [cocode_symm, cocode_apply, loopInverse_sign, psi3_sign] at hm
  have hd : psi3N (loopInverse d) * psi2N (loopInverse d) = psi1N d := by
    have h := psi3N_mul_psi2N_mul_psi1N (loopInverse d)
    calc
      _ = (psi1N (loopInverse d))⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = psi1N d := by rw [psi1N_inv, loopInverse_inverse]
  apply Subtype.ext
  simp only [signConjugation, q1Conjugation_val, Subgroup.coe_mul, cocode_val,
    third_val, first_val]
  rw [← hm, psi2_inv]
  simpa only [mul_assoc] using congrArg
    (fun x : N => psiAut1N (parkerCocodeStandard c) *
      (psi3N (0,cocodePairing d.1 c) * x)) hd

end Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation

namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin TrialityGeneratorCalculation

private theorem half_smul_one_left (s : Bit) (a : golay) :
    golayHalfOverlap (s • golayOne) a = 0 := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl <;> simp [golayHalfOverlap_one]

private theorem half_smul_one_right (a : golay) (s : Bit) :
    golayHalfOverlap a (s • golayOne) = 0 := by
  rw [golayHalfOverlap_symmetric, half_smul_one_left]

private theorem half_smul_one_add_left (s : Bit) (a b : golay) :
    golayHalfOverlap (s • golayOne + a) b = golayHalfOverlap a b := by
  rw [add_comm (s • golayOne), golayHalfOverlap_add_smul_one_left]

private theorem half_smul_one_add_right (a b : golay) (s : Bit) :
    golayHalfOverlap a (s • golayOne + b) = golayHalfOverlap a b := by
  rw [add_comm (s • golayOne), golayHalfOverlap_add_smul_one_right]

/-- Exercise 4.6(4): conjugation by the second Parker family induces the
source sign change, on both code and cocode and for either cocode parity. -/
theorem q1Coordinates_conjugation_psi2 (d : ParkerLoop) (q : Q1) :
    (q1Coordinates (q1Conjugation ⟨psi2N d, psi2N_mem_N1 d⟩ q)).toAdd =
      sourceSignCoordinates d.1 (q1Coordinates q).toAdd := by
  obtain ⟨⟨e,t,c⟩,rfl⟩ := q1Param_bijective.surjective q
  rw [q1Coordinates_param]
  change coordinates (signConjugation d (q1Param (e,t,c))) =
    sourceSignCoordinates d.1 (q1WordCoordinates e t c)
  rw [param_eq]
  have hp : cocodeParity c = 0 ∨ cocodeParity c = 1 := by
    generalize cocodeParity c = p
    revert p
    decide
  rcases hp with hp | hp
  · simp only [map_mul, signConjugation_cocode_even d c hp, signConjugation_sign,
      signConjugation_first, coordinates_mul, first_coordinates, sign_coordinates,
      third_coordinates, cocode_coordinates]
    apply QuadraticCoordinates.ext
    · simp [quadraticCoordinates_add_eq, coordinateSum, sourceSignCoordinates,
        q1WordCoordinates, hp, half_smul_one_left, half_smul_one_right,
        half_smul_one_add_right,
        golayHalfOverlap_symmetric e.1 d.1, add_smul]
      module
    · simp [quadraticCoordinates_add_eq, coordinateSum, sourceSignCoordinates,
        q1WordCoordinates, hp, intersectionCocode_add_left, intersectionCocode_add_right,
        intersectionCocode_comm e.1 d.1]
  · have hn : cocodeParity c ≠ 0 := by rw [hp]; exact one_ne_zero
    simp only [map_mul, signConjugation_cocode_odd d c hn, signConjugation_sign,
      signConjugation_first, coordinates_mul, first_coordinates, sign_coordinates,
      third_coordinates, cocode_coordinates]
    apply QuadraticCoordinates.ext
    · simp [quadraticCoordinates_add_eq, coordinateSum, sourceSignCoordinates,
        q1WordCoordinates, hp, half_smul_one_left, half_smul_one_right,
        half_smul_one_add_left, half_smul_one_add_right,
        golayHalfOverlap_symmetric e.1 d.1]
      match_scalars <;> ring_nf
      simp
    · simp [quadraticCoordinates_add_eq, coordinateSum, sourceSignCoordinates,
        q1WordCoordinates, hp, intersectionCocode_add_left, intersectionCocode_add_right,
        intersectionCocode_comm e.1 d.1, add_assoc]
      rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul Bit]
      exact zero_smul Bit _

end Sporadic.Monster.Construction.LocalC
namespace Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation
open TrialitySpin

private theorem pairing_permutation (σ : Mathieu24CodeModel) (v : golay) (c : Cocode) :
    cocodePairing (parkerCodeEquiv σ v) (sourceCocodePermutation σ c) =
      cocodePairing v c := by
  obtain ⟨J,rfl⟩ := Submodule.Quotient.mk_surjective golay c
  rw [sourceCocodePermutation_mk, cocodePairing, cocodePairing,
    cocodeDualEquiv_mk, cocodeDualEquiv_mk]
  exact Equiv.sum_comp σ.val.symm (fun p => v.val p * J p)

private theorem standard_cocode_interchange (α : ParkerStandardGroup) (c : Cocode) :
    α * parkerCocodeStandard c =
      parkerCocodeStandard (sourceCocodePermutation (parkerStandardProjection α) c) * α := by
  apply Subtype.ext
  ext d : 1
  change α.val ((parkerCocodeStandard c).val d) =
    (parkerCocodeStandard (sourceCocodePermutation (parkerStandardProjection α) c)).val
      (α.val d)
  rw [cocode_apply, parkerStandard_preserves_sign, cocode_apply,
    parkerStandardProjection_spec, pairing_permutation]

private def permutationConjugation (α : ParkerStandardGroup) : MulAut Q1 :=
  q1Conjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩

private theorem permutationConjugation_cocode (α : ParkerStandardGroup) (c : Cocode) :
    permutationConjugation α (cocode c) =
      cocode (sourceCocodePermutation (parkerStandardProjection α) c) := by
  have hm := congrArg psiAut1N (standard_cocode_interchange α c)
  simp only [aut_mul] at hm
  apply Subtype.ext
  simp only [permutationConjugation, q1Conjugation_val, cocode_val]
  rw [hm, mul_inv_cancel_right]

private theorem permutationConjugation_first_coordinates (α : ParkerStandardGroup) (d : ParkerLoop) :
    coordinates (permutationConjugation α (first d)) =
      ⟨parkerCodeEquiv (parkerStandardProjection α) d.1,0⟩ := by
  by_cases hα : α.val parkerOmega = parkerOmega
  · have h : permutationConjugation α (first d) = first (α.val d) := by
      apply Subtype.ext
      simp only [permutationConjugation, q1Conjugation_val, first_val]
      rw [aut_psi1_even α hα, mul_inv_cancel_right]
    rw [h, first_coordinates, parkerStandardProjection_spec]
  · have h : permutationConjugation α (first d) = first (α.val (loopInverse d)) := by
      apply Subtype.ext
      simp only [permutationConjugation, q1Conjugation_val, first_val]
      rw [aut_psi1_odd α hα, mul_inv_cancel_right]
    rw [h, first_coordinates, parkerStandardProjection_spec]
    rfl

private theorem permutationConjugation_sign_coordinates (α : ParkerStandardGroup) (t : ParkerBit) :
    coordinates (permutationConjugation α (sign t)) = ⟨t • golayOne,0⟩ := by
  by_cases hα : α.val parkerOmega = parkerOmega
  · have h : permutationConjugation α (sign t) = sign t := by
      apply Subtype.ext
      simp only [permutationConjugation, q1Conjugation_val, sign_val]
      rw [aut_psi2_even α hα, α.prop.2.1, mul_inv_cancel_right]
    rw [h, sign_coordinates]
  · have h : permutationConjugation α (sign t) = third t := by
      apply Subtype.ext
      simp only [permutationConjugation, q1Conjugation_val, sign_val, third_val]
      rw [aut_psi2_odd α hα]
      have hi : loopInverse (0,t) = (0,t) := by
        simp [loopInverse]
      rw [hi, α.prop.2.1, mul_inv_cancel_right]
    rw [h, third_coordinates]

end Sporadic.Monster.Construction.LocalC.TrialityGeneratorCalculation

namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin TrialityGeneratorCalculation

/-- Exercise 4.6(4): every standard automorphism induces its actual Golay
coordinate permutation, including the odd automorphisms. -/
theorem q1Coordinates_conjugation_psiAut1 (α : ParkerStandardGroup) (q : Q1) :
    (q1Coordinates (q1Conjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ q)).toAdd =
      sourcePermutationCoordinates (parkerStandardProjection α) (q1Coordinates q).toAdd := by
  obtain ⟨⟨d,t,c⟩,rfl⟩ := q1Param_bijective.surjective q
  rw [q1Coordinates_param]
  change coordinates (permutationConjugation α (q1Param (d,t,c))) =
    sourcePermutationCoordinates (parkerStandardProjection α) (q1WordCoordinates d t c)
  rw [param_eq]
  simp only [map_mul, coordinates_mul, permutationConjugation_cocode,
    permutationConjugation_first_coordinates, permutationConjugation_sign_coordinates,
    cocode_coordinates]
  apply QuadraticCoordinates.ext
  · simp only [quadraticCoordinates_add_eq, coordinateSum, sourcePermutationCoordinates,
      q1WordCoordinates, map_add, map_smul, parkerCodeEquiv_golayOne,
      zero_add, add_zero, golayHalfOverlap_zero_left, zero_smul, half_smul_one_left]
    exact add_comm _ _
  · simp only [quadraticCoordinates_add_eq, coordinateSum, sourcePermutationCoordinates,
      q1WordCoordinates, zero_add, add_zero, golayHalfOverlap_zero_left, zero_smul,
      intersectionCocode_zero_left, intersectionCocode_smul_one_left]

end Sporadic.Monster.Construction.LocalC
