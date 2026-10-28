module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.Forms
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.DirectSumAction

/-!
# The exact cubic coefficients on the three zero summands

The mixed block `sourceRWW` evaluates on the literal odd short lift and the
two half-spin tensor inclusions. The marked integer Leech coordinates give
`(4 delta_xy - a_x a_y)/32`, multiplied by the actual spin matrix coefficient.
For `r(z,1)`, the actual cocode spin operator exchanges `delta2(1)` and
`delta3(1)`. This proves the three standard coefficients of 29.9 directly
for the fixed `griessBeta`: -1/32, 3/32, and -5/32 according to the equality
pattern of the marked coordinates.

The vectors retain the normalization in `Forms`; no cubic is replaced or
averaged. The ordered evaluation has exactly the one `R,W,W` block, since
its first vector is short and the other two are in the minus space. Thus
there is no extra factor of six in the displayed coefficients. Reducing all
nonzero coefficients to these representatives under the group action remains
a separate assertion.

Source: Aschbacher, *Sporadic Groups*, 28.6, 28.11 and the proof of 29.9,
printed pp. 153 and 158 (PDF page 85, left). The scanned expressions are
`(1-a_x^2/4)/8` and `-a_x*a_y/32`.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct BigOperators Matrix
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

def oddCoordinate (z : Omega) (b : ParkerLoop) (x : Omega) : ℝ :=
  ((oddRepresentative z b).val x : ℝ)

theorem pointVector_dot (x : Omega) (v : NaturalSpace) :
    pointVector x ⬝ᵥ v = v (coordinateMarking.symm x) := by
  simp [pointVector, dotProduct, Pi.single_apply]

theorem dot_pointVector (v : NaturalSpace) (x : Omega) :
    v ⬝ᵥ pointVector x = v (coordinateMarking.symm x) := by
  rw [dotProduct_comm, pointVector_dot]

theorem pointVector_dot_pointVector (x y : Omega) :
    pointVector x ⬝ᵥ pointVector y = if x = y then 1 else 0 := by
  rw [pointVector_dot]
  simp [pointVector, Pi.single_apply, coordinateMarking.symm.injective.eq_iff]

theorem pointVector_dot_odd (x z : Omega) (b : ParkerLoop) :
    pointVector x ⬝ᵥ leechVector (oddRepresentative z b) =
      oddCoordinate z b x / Real.sqrt 8 := by
  rw [pointVector_dot]
  simp [leechVector, oddCoordinate]

theorem griessBeta_odd_two_three (z : Omega) (b : ParkerLoop) (x y : Omega)
    (s : B1A2) (t : B1A3) :
    griessBeta (zeroInclusion (zeroOdd z b))
      (zeroInclusion (zeroTwo (pointVector x) s))
      (zeroInclusion (zeroThree (pointVector y) t)) =
      ((if x = y then 4 else 0) - oddCoordinate z b x * oddCoordinate z b y) / 32 *
        bothAxesDomain.form
          (SpinAction.imageRepresentation (rOdd z b).val (spinRestriction.symm (s,0)))
          (spinRestriction.symm (0,t)) := by
  rw [zeroInclusion_odd, zeroInclusion_two, zeroInclusion_three,
    griessBeta_RWW (rOdd z b) (oddShell z b) (rOdd_class z b).symm]
  simp only [oddShell]
  rw [pointVector_dot_pointVector, pointVector_dot_odd, dotProduct_comm (leechVector _),
    pointVector_dot_odd]
  have hs : Real.sqrt (8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (8 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  change ((if x = y then 1 else 0) -
    2 * (oddCoordinate z b x / Real.sqrt 8) * (oddCoordinate z b y / Real.sqrt 8)) * _ / 8 = _
  split_ifs <;> field_simp <;> rw [hs] <;> ring

theorem oddCoordinate_one (z x : Omega) :
    oddCoordinate z loopOne x = if x = z then 3 else -1 := by
  unfold oddCoordinate
  rw [oddRepresentative_apply]
  have hc : oddCode z loopOne = 0 := by simp [oddCode, loopOne]
  rw [hc]
  simp only [golayIntegerLift, Submodule.coe_zero, Pi.zero_apply]
  split_ifs <;> norm_num


theorem loopImage_one : loopImage loopOne = 1 := by
  apply Subtype.ext
  rw [loopImage_val, TrialityGeneratorCalculation.psi1_one, map_one]
  rfl

theorem rOddElement_one (z : Omega) : rOddElement z loopOne = cocodeImage (pointWord z) := by
  rw [rOddElement, loopImage_one]
  simp [loopOne]

theorem pointStandard_odd (z : Omega) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pointWord z))).val parkerOmega ≠
      parkerOmega := by
  intro h
  rw [parkerCocodeStandard_apply] at h
  have hh := congrArg Prod.snd h
  change 0 + cocodePairing golayOne (Submodule.Quotient.mk (pointWord z)) = 0 at hh
  rw [zero_add, cocodePairing, cocodeDualEquiv_mk] at hh
  simp [golayOne, pointWord, binaryDot_apply, allOnes, Pi.single_apply] at hh

theorem pointStandard_one (z : Omega) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pointWord z))).val loopOne = loopOne := by
  rw [parkerCocodeStandard_apply]
  change (0, (0 : ParkerBit) + cocodeDualEquiv _ 0) = (0,0)
  rw [map_zero, add_zero]

theorem oddSpin_one (z : Omega) :
    SpinAction.imageRepresentation (rOdd z loopOne).val
      (spinRestriction.symm (delta2 loopOne,0)) =
        spinRestriction.symm (0,delta3 loopOne) := by
  have hq : cocodeImage (pointWord z) = q1ImageMap
      ⟨psiAut1N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord z))),
        psiAut1N_mem_Q1_of_sign _ ((parkerStandardProjection_eq_one_iff _).mp
          (parkerCocodeStandard_projection _))⟩ := by
    apply Subtype.ext
    exact cocodeImage_val _
  rw [rOdd_val, rOddElement_one, hq, SpinAction.imageRepresentation_map]
  change SpinAction.representation
    (DirectSumAction.standard (parkerCocodeStandard (Submodule.Quotient.mk (pointWord z))))
      (spinRestriction.symm (delta2 loopOne,0)) = _
  apply spinRestriction.injective
  rw [← DirectSumAction.representation_restriction, spinRestriction.apply_symm_apply,
    spinRestriction.apply_symm_apply,
    DirectSumAction.representation_odd_delta2 _ (pointStandard_odd z), pointStandard_one]
  simp [loopOne, golayQuarterWeight]

theorem oddSpin_one_pairing (z : Omega) :
    bothAxesDomain.form
      (SpinAction.imageRepresentation (rOdd z loopOne).val
        (spinRestriction.symm (delta2 loopOne,0)))
      (spinRestriction.symm (0,delta3 loopOne)) = 1 := by
  rw [oddSpin_one, ← spinRestriction_isometry]
  simp [delta3_norm]


/-- The coefficient of the three source standard vectors, without rescaling. -/
theorem griessBeta_standard (z x y : Omega) :
    griessBeta (zeroInclusion (zeroOdd z loopOne))
      (zeroInclusion (zeroTwo (pointVector x) (delta2 loopOne)))
      (zeroInclusion (zeroThree (pointVector y) (delta3 loopOne))) =
      if x = y ∧ y = z then (-5 : ℝ) / 32
      else if x = y ∨ x = z ∨ y = z then (3 : ℝ) / 32 else (-1 : ℝ) / 32 := by
  rw [griessBeta_odd_two_three, oddSpin_one_pairing, mul_one,
    oddCoordinate_one, oddCoordinate_one]
  by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;>
    simp_all <;> norm_num

end Sporadic.Monster.Construction.NMonomial.ZeroAction
