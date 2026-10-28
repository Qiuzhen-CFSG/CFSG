module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.CubicInvariance.Marked
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.HalfComparisons

/-!
# Vanishing blocks on the three marked zero summands

The cocode parity of the actual extraspecial coordinates is additive because
Golay intersections have even parity. Every odd short lift has parity one,
whereas both central elements have parity zero. Thus three odd lifts have
zero coefficient in the short cubic block.

For the remaining exceptional blocks, the actual odd spin operator exchanges
the two half-spin spaces: its point-cocode factor exchanges them, and its
loop factors preserve them. Their orthogonality kills an odd vector paired
with two vectors from the same half. The five-block form kills triples with
two odd vectors and one spin vector, and triples wholly in the spin part.
Symmetry assembles these into vanishing whenever a marked summand repeats.

Source: Aschbacher, *Sporadic Groups*, 9.3, 28.4, 28.6, 28.11, 29.2(4),
and the first paragraph of the proof of 29.9, printed p. 158 (PDF p. 85).
This verifies the source support restriction directly on the fixed cubic;
it uses no invariance or monomial-reduction premise for N.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

private def oddParity (q : Q1Image) : ParkerBit :=
  cocodeParity (q1ImageCoordinates q).toAdd.cocode
private theorem oddParity_mul (q r : Q1Image) :
    oddParity (q * r) = oddParity q + oddParity r := by
  unfold oddParity
  rw [map_mul]
  change cocodeParity ((q1ImageCoordinates q).toAdd.cocode +
    (q1ImageCoordinates r).toAdd.cocode +
    intersectionCocode (q1ImageCoordinates q).toAdd.code
      (q1ImageCoordinates r).toAdd.code) = _
  simp
private theorem oddParity_one : oddParity 1 = 0 := by simp [oddParity]; rfl
private theorem oddParity_center : oddParity q1ImageCenterGenerator = 0 := by
  have h : q1ImageCoordinates q1ImageCenterGenerator = 1 := by
    change q1ImageCenterGenerator ∈ q1ImageCoordinates.ker
    rw [q1ImageCoordinates_kernel]
    exact centerGenerator_mem
  simp [oddParity, h]
  rfl
private theorem oddParity_loop (d : ParkerLoop) : oddParity (loopImage d) = 0 := by
  simp [oddParity, loopImage, q1WordCoordinates]
private theorem oddParity_point (x : Omega) : oddParity (cocodeImage (pointWord x)) = 1 := by
  simp [oddParity, cocodeImage, q1WordCoordinates, cocodeParity_mk,
    pointWord, binaryDot_apply, golayOne, allOnes, Pi.single_apply]
private theorem oddParity_odd (x : Omega) (d : ParkerLoop) : oddParity (rOdd x d).val = 1 := by
  rw [rOdd_val, rOddElement, oddParity_mul, oddParity_mul, oddParity_loop,
    oddParity_point, zero_add]
  rcases bit_cases (d.1.val x) with h | h
  · rw [h]; exact (congrArg (· + 1) oddParity_one).trans (zero_add 1)
  · rw [h]; change oddParity (loopImage parkerOmega ^ 1) + 1 = 1
    rw [pow_one, oddParity_loop, zero_add]

private theorem odd_cubic_zero (x y z : Omega) (b c d : ParkerLoop) :
    Griess.shortCoefficient sourceLatticeComparison (rOdd x b) (rOdd y c) (rOdd z d) = 0 := by
  have hp : oddParity ((rOdd x b).val * (rOdd y c).val * (rOdd z d).val) = 1 := by
    rw [oddParity_mul, oddParity_mul, oddParity_odd, oddParity_odd, oddParity_odd]
    decide
  have h1 : (rOdd x b).val * (rOdd y c).val * (rOdd z d).val ≠ 1 := by
    intro h
    rw [h, oddParity_one] at hp
    exact zero_ne_one hp
  have hz : (rOdd x b).val * (rOdd y c).val * (rOdd z d).val ≠ q1ImageCenterGenerator := by
    intro h
    rw [h, oddParity_center] at hp
    exact zero_ne_one hp
  simp only [Griess.shortCoefficient, Griess.centralCoefficient, h1, hz, if_false, sub_self]

private def spinOn (q : Q1Image) : Module.End ℝ SpinDirectSum :=
  spinRestriction.toLinearMap.comp
    ((SpinAction.imageRepresentation q).comp spinRestriction.symm.toLinearMap)
private theorem spinOn_mul (q r : Q1Image) (v : SpinDirectSum) :
    spinOn (q * r) v = spinOn q (spinOn r v) := by
  simp [spinOn, map_mul, Module.End.mul_apply]
private theorem spinOn_one (v : SpinDirectSum) : spinOn 1 v = v := by
  simp [spinOn]
private theorem spinOn_loop (d : ParkerLoop) (v : SpinDirectSum) :
    spinOn (loopImage d) v =
      (HalfActions.secondRepresentation (HalfActions.psiOne d) v.1,
        HalfActions.thirdRepresentation (HalfActions.psiOne d) v.2) := by
  have h : SpinAction.imageRepresentation (loopImage d) =
      SpinAction.representation (HalfActions.inclusion (HalfActions.psiOne d)) := by
    rw [loopImage, SpinAction.imageRepresentation_map]
    change SpinAction.representation (SpinAction.q1Inclusion (q1Param (d,0,0))) = _
    congr 1
    apply Subtype.ext
    change (q1Word d 0 0).val = psi1N d
    rw [q1Word_cocode_zero]
    change psi2N loopOne * psi1N d = psi1N d
    rw [TrialityGeneratorCalculation.psi2_one, one_mul]
  change spinRestriction (SpinAction.imageRepresentation (loopImage d)
    (spinRestriction.symm v)) = _
  rw [h, ← DirectSumAction.representation_restriction, spinRestriction.apply_symm_apply,
    DirectSumAction.representation_even]
private theorem spinOn_point (x : Omega) (v : SpinDirectSum) :
    spinOn (cocodeImage (pointWord x)) v =
      (psiAut1OddBack _ (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))).prop
        (pointStandard_odd x) v.2,
       psiAut1Odd _ (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))).prop
        (pointStandard_odd x) v.1) := by
  have hq : cocodeImage (pointWord x) = q1ImageMap
      ⟨psiAut1N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))),
        psiAut1N_mem_Q1_of_sign _ ((parkerStandardProjection_eq_one_iff _).mp
          (parkerCocodeStandard_projection _))⟩ := by
    apply Subtype.ext
    exact cocodeImage_val _
  change spinRestriction (SpinAction.imageRepresentation (cocodeImage (pointWord x))
    (spinRestriction.symm v)) = _
  rw [hq, SpinAction.imageRepresentation_map]
  change spinRestriction (SpinAction.representation
    (DirectSumAction.standard (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))))
      (spinRestriction.symm v)) = _
  rw [← DirectSumAction.representation_restriction, spinRestriction.apply_symm_apply,
    DirectSumAction.representation_odd]

private theorem oddSpin_two_fst (x : Omega) (d : ParkerLoop) (s : B1A2) :
    (spinRestriction (SpinAction.imageRepresentation (rOdd x d).val
      (spinRestriction.symm (s,0)))).1 = 0 := by
  change (spinOn (rOdd x d).val (s,0)).1 = 0
  rw [rOdd_val, rOddElement, spinOn_mul, spinOn_mul, spinOn_loop, spinOn_point]
  rcases bit_cases (d.1.val x) with h | h <;>
    simp only [h, show (0 : ParkerBit).val = 0 from rfl,
      show (1 : ParkerBit).val = 1 from rfl, pow_zero, pow_one, spinOn_one,
      spinOn_loop, map_zero]
private theorem oddSpin_three_snd (x : Omega) (d : ParkerLoop) (s : B1A3) :
    (spinRestriction (SpinAction.imageRepresentation (rOdd x d).val
      (spinRestriction.symm (0,s)))).2 = 0 := by
  change (spinOn (rOdd x d).val (0,s)).2 = 0
  rw [rOdd_val, rOddElement, spinOn_mul, spinOn_mul, spinOn_loop, spinOn_point]
  rcases bit_cases (d.1.val x) with h | h <;>
    simp only [h, show (0 : ParkerBit).val = 0 from rfl,
      show (1 : ParkerBit).val = 1 from rfl, pow_zero, pow_one, spinOn_one,
      spinOn_loop, map_zero]
private theorem oddSpin_two_pairing (x : Omega) (d : ParkerLoop) (s t : B1A2) :
    bothAxesDomain.form
      (SpinAction.imageRepresentation (rOdd x d).val (spinRestriction.symm (s,0)))
      (spinRestriction.symm (t,0)) = 0 := by
  rw [← spinRestriction_isometry, spinRestriction.apply_symm_apply, oddSpin_two_fst]
  simp
private theorem oddSpin_three_pairing (x : Omega) (d : ParkerLoop) (s t : B1A3) :
    bothAxesDomain.form
      (SpinAction.imageRepresentation (rOdd x d).val (spinRestriction.symm (0,s)))
      (spinRestriction.symm (0,t)) = 0 := by
  rw [← spinRestriction_isometry, spinRestriction.apply_symm_apply, oddSpin_three_snd]
  simp

variable (e : oddSpace ≃ₗ[ℝ] TensorTwo)
  (he : ∀ x b, e (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b)
include he

/-- Three odd short lifts have odd cocode parity, so their product is noncentral. -/
theorem modelBeta_odd_odd_odd (x y z : Omega) (b c d : ParkerLoop) :
    modelBeta e (modelOdd x b) (modelOdd y c) (modelOdd z d) = 0 := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_odd e he,
    modelInclusion_odd e he, zeroInclusion_odd, zeroInclusion_odd, zeroInclusion_odd]
  change Griess.sourceBeta sourceLatticeComparison _ _ _ = 0
  rw [Griess.sourceBeta_RRR, Griess.shortCubic_vector, odd_cubic_zero]

/-- The actual odd spin operator exchanges the halves; they are orthogonal. -/
theorem modelBeta_odd_two_two (x : Omega) (d : ParkerLoop)
    (a b : NaturalSpace) (s t : B1A2) :
    modelBeta e (modelOdd x d) (modelTwo a s) (modelTwo b t) = 0 := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_two,
    modelInclusion_two, zeroInclusion_odd, zeroInclusion_two, zeroInclusion_two,
    griessBeta_RWW (rOdd x d) (oddShell x d) (rOdd_class x d).symm,
    oddSpin_two_pairing, mul_zero, zero_div]

/-- The corresponding exclusion on the other literal spin half. -/
theorem modelBeta_odd_three_three (x : Omega) (d : ParkerLoop)
    (a b : NaturalSpace) (s t : B1A3) :
    modelBeta e (modelOdd x d) (modelThree a s) (modelThree b t) = 0 := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_three,
    modelInclusion_three, zeroInclusion_odd, zeroInclusion_three, zeroInclusion_three,
    griessBeta_RWW (rOdd x d) (oddShell x d) (rOdd_class x d).symm,
    oddSpin_three_pairing, mul_zero, zero_div]

private theorem modelBeta_odd_odd_two (x y : Omega) (b c : ParkerLoop)
    (a : NaturalSpace) (s : B1A2) :
    modelBeta e (modelOdd x b) (modelOdd y c) (modelTwo a s) = 0 := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_odd e he,
    modelInclusion_two, zeroInclusion_odd, zeroInclusion_odd, zeroInclusion_two]
  exact Griess.sourceBeta_RRW sourceLatticeComparison _ _ _

private theorem modelBeta_odd_odd_three (x y : Omega) (b c : ParkerLoop)
    (a : NaturalSpace) (s : B1A3) :
    modelBeta e (modelOdd x b) (modelOdd y c) (modelThree a s) = 0 := by
  rw [modelBeta_inclusion, modelInclusion_odd e he, modelInclusion_odd e he,
    modelInclusion_three, zeroInclusion_odd, zeroInclusion_odd, zeroInclusion_three]
  exact Griess.sourceBeta_RRW sourceLatticeComparison _ _ _

/-- Every repeated marked summand gives a zero coefficient, including all-odd
and the two same-half mixed blocks. Symmetry supplies the other orderings. -/
theorem modelBeta_repeated_mark (i j : Fin 3) (x y z : Omega) (b c d : ParkerLoop) :
    modelBeta e (markedVector i x b) (markedVector i y c) (markedVector j z d) = 0 := by
  fin_cases i <;> fin_cases j
  · exact modelBeta_odd_odd_odd e he x y z b c d
  · exact modelBeta_odd_odd_two e he x y b c _ _
  · exact modelBeta_odd_odd_three e he x y b c _ _
  · rw [modelBeta_swap_outer, modelBeta_swap_right]
    exact modelBeta_odd_two_two e he z d _ _ _ _
  · change modelBeta e (modelTwo _ _) (modelTwo _ _) (modelTwo _ _) = 0
    rw [modelBeta_inclusion, modelInclusion_two, modelInclusion_two,
      modelInclusion_two, zeroInclusion_two, zeroInclusion_two, zeroInclusion_two]
    exact Griess.sourceBeta_WWW sourceLatticeComparison _ _ _
  · rw [modelBeta_inclusion]
    change griessBeta (modelInclusion e (modelTwo _ _))
      (modelInclusion e (modelTwo _ _)) (modelInclusion e (modelThree _ _)) = 0
    rw [modelInclusion_two, modelInclusion_two, modelInclusion_three,
      zeroInclusion_two, zeroInclusion_two, zeroInclusion_three]
    exact Griess.sourceBeta_WWW sourceLatticeComparison _ _ _
  · rw [modelBeta_swap_outer, modelBeta_swap_right]
    exact modelBeta_odd_three_three e he z d _ _ _ _
  · rw [modelBeta_inclusion]
    change griessBeta (modelInclusion e (modelThree _ _))
      (modelInclusion e (modelThree _ _)) (modelInclusion e (modelTwo _ _)) = 0
    rw [modelInclusion_three, modelInclusion_three, modelInclusion_two,
      zeroInclusion_three, zeroInclusion_three, zeroInclusion_two]
    exact Griess.sourceBeta_WWW sourceLatticeComparison _ _ _
  · rw [modelBeta_inclusion]
    change griessBeta (modelInclusion e (modelThree _ _))
      (modelInclusion e (modelThree _ _)) (modelInclusion e (modelThree _ _)) = 0
    rw [modelInclusion_three, modelInclusion_three, modelInclusion_three,
      zeroInclusion_three, zeroInclusion_three, zeroInclusion_three]
    exact Griess.sourceBeta_WWW sourceLatticeComparison _ _ _

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
