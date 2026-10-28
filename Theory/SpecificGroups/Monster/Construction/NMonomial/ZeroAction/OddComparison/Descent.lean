module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Spanning

/-!
# Signed descent of the odd short family

Evaluation at the literal lifts r(x,b) gives a signed function on the actual
second-axis Omega orbits. The proved parameter relations make this descend;
comparison of the signed delta coefficients sends each shortVector(r(x,b))
to pointVector x tensor delta2 b. The forms agree on these spanning families.
Positivity proves injectivity and spanning proves surjectivity, without a
dimension comparison or a chosen bijection of abstract bases.

Source: Aschbacher, Sporadic Groups, 27.8(3) and the well-definedness argument
of 29.8, printed pp. 150 and 157 (PDF pages 81 and 84). This module constructs
the linear isometry; the source conjugation calculation is a separate step.
-/

public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions SignedModules
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction


private theorem pairing_axis (b : ParkerLoop) :
    secondAxisDomain.pairing.flip (axis2Equiv b) =
      axis2Equiv (parkerLoopMultiply b parkerOmega) := Subtype.ext (k1_axis2 b)

private theorem signs_axis (b : ParkerLoop) :
    secondAxisDomain.signs.flip (axis2Equiv b) =
      axis2Equiv (parkerSign 1 b) := Subtype.ext (z1_axis2 b)

private def oddCoefficient (v : Space) (x : Omega) :
    secondAxisDomain.pairing.Orbit → ℝ :=
  Quotient.lift (fun a => v.val (rOdd x (axis2Equiv.symm a))) (by
    intro a b hab
    rcases hab with rfl | rfl
    · rfl
    · obtain ⟨b,rfl⟩ := axis2Equiv.surjective b
      simp only [pairing_axis, Equiv.symm_apply_apply, rOdd_mul_omega])

private theorem oddCoefficient_axis (v : Space) (x : Omega) (b : ParkerLoop) :
    oddCoefficient v x (secondAxisDomain.pairing.orbit (axis2Equiv b)) =
      v.val (rOdd x b) := by
  change v.val (rOdd x (axis2Equiv.symm (axis2Equiv b))) = _
  rw [Equiv.symm_apply_apply]

private def oddCoordinates : Space →ₗ[ℝ] (Fin 24 → B1A2) where
  toFun v i := ⟨oddCoefficient v (coordinateMarking i), by
    intro a
    induction a using Quotient.inductionOn with
    | h a =>
      obtain ⟨b,rfl⟩ := axis2Equiv.surjective a
      change oddCoefficient v (coordinateMarking i)
        (secondAxisDomain.pairing.orbit (secondAxisDomain.signs.flip (axis2Equiv b))) =
          -oddCoefficient v (coordinateMarking i) (secondAxisDomain.pairing.orbit (axis2Equiv b))
      rw [signs_axis, oddCoefficient_axis, oddCoefficient_axis, rOdd_sign]
      exact v.property _⟩
  map_add' v w := by
    funext i
    apply Subtype.ext
    funext a
    induction a using Quotient.inductionOn with
    | h a => rfl
  map_smul' c v := by
    funext i
    apply Subtype.ext
    funext a
    induction a using Quotient.inductionOn with
    | h a => rfl

private theorem delta2_apply (b c : ParkerLoop) :
    (delta2 b).val (secondAxisDomain.pairing.orbit (axis2Equiv c)) =
      (if c = b ∨ c = parkerLoopMultiply b parkerOmega then 1 else 0) -
        (if c = parkerSign 1 b ∨ c = parkerSign 1 (parkerLoopMultiply b parkerOmega)
          then 1 else 0) := by
  change (secondAxisDomain.signedOrbits.delta
    (secondAxisDomain.pairing.orbit (axis2Equiv b))).val _ = _
  rw [SignedSet.delta_apply]
  have hz : secondAxisDomain.signedOrbits.flip
      (secondAxisDomain.pairing.orbit (axis2Equiv b)) =
      secondAxisDomain.pairing.orbit (secondAxisDomain.signs.flip (axis2Equiv b)) := rfl
  rw [hz]
  rw [signs_axis]
  have ho (d e : ParkerLoop) :
      secondAxisDomain.pairing.orbit (axis2Equiv d) =
        secondAxisDomain.pairing.orbit (axis2Equiv e) ↔
      d = e ∨ d = parkerLoopMultiply e parkerOmega := by
    refine (secondAxisDomain.pairing.orbit_eq _ _).trans ?_
    rw [pairing_axis]
    exact or_congr axis2Equiv.injective.eq_iff axis2Equiv.injective.eq_iff
  rw [ho, ho, parkerLoopMultiply_sign_left]
  split_ifs <;> rfl

private theorem oddCoordinates_vector (x : Omega) (b : ParkerLoop) :
    oddCoordinates (shortVector sourceLatticeComparison (rOdd x b)) =
      tensorCoordinates B1A2 (pointVector x ⊗ₜ[ℝ] delta2 b) := by
  funext i
  apply Subtype.ext
  funext a
  induction a using Quotient.inductionOn with
  | h a =>
    obtain ⟨c,rfl⟩ := axis2Equiv.surjective a
    change oddCoefficient (shortVector sourceLatticeComparison (rOdd x b))
      (coordinateMarking i) (secondAxisDomain.pairing.orbit (axis2Equiv c)) =
      (pointVector x i) * (delta2 b).val (secondAxisDomain.pairing.orbit (axis2Equiv c))
    rw [oddCoefficient_axis]
    change (if rOdd (coordinateMarking i) c = rOdd x b then 1 else 0) -
      (if rOdd (coordinateMarking i) c = (shortLiftSigns sourceLatticeComparison).flip
        (rOdd x b) then 1 else 0) = _
    simp only [rOdd_eq_iff, rOdd_eq_flip_iff, delta2_apply]
    by_cases hi : i = coordinateMarking.symm x
    · subst i
      simp [pointVector]
    · have hx : coordinateMarking i ≠ x := fun h => hi (coordinateMarking.eq_symm_apply.mpr h)
      simp [pointVector, Pi.single_eq_of_ne hi, hx]

/-- Coordinate restriction to the literal signed odd family. -/
def oddToTensor : oddSpace →ₗ[ℝ] TensorTwo :=
  (tensorCoordinates B1A2).symm.toLinearMap.comp (oddCoordinates.comp oddSpace.subtype)

theorem oddToTensor_vector (x : Omega) (b : ParkerLoop) :
    oddToTensor (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b := by
  change (tensorCoordinates B1A2).symm
    (oddCoordinates (shortVector sourceLatticeComparison (rOdd x b))) = _
  rw [oddCoordinates_vector, LinearEquiv.symm_apply_apply]

-- Keep the concrete quotient coordinate map out of subsequent instance search.
attribute [local irreducible] oddToTensor

private theorem form_marked (x y : Omega) (b c : ParkerLoop) :
    tensorTwoForm (pointVector x ⊗ₜ[ℝ] delta2 b) (pointVector y ⊗ₜ[ℝ] delta2 c) =
      shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOdd x b))
        (shortVector sourceLatticeComparison (rOdd y c)) := by
  rw [tensorTwoForm, LinearMap.BilinForm.tensorDistrib_tmul, form_vector]
  have hf : secondAxisDomain.form (delta2 b) (delta2 c) =
      (delta2 c).val (secondAxisDomain.pairing.orbit (axis2Equiv b)) :=
    secondAxisDomain.signedOrbits.form_delta _ _
  rw [hf, delta2_apply]
  change _ * naturalForm (Pi.single (coordinateMarking.symm x) 1)
    (Pi.single (coordinateMarking.symm y) 1) = _
  rw [← Pi.basisFun_apply, ← Pi.basisFun_apply, naturalForm_basis]
  simp only [coordinateMarking.symm.injective.eq_iff, rOdd_eq_iff, rOdd_eq_flip_iff]
  by_cases h : x = y <;> simp [h]

theorem oddToTensor_isometry (v w : oddSpace) :
    tensorTwoForm (oddToTensor v) (oddToTensor w) =
      shortForm sourceLatticeComparison v.val w.val := by
  have he : tensorTwoForm.compl₁₂ oddToTensor oddToTensor =
      (shortForm sourceLatticeComparison).compl₁₂ oddSpace.subtype oddSpace.subtype := by
    apply oddSpace_ext
    intro x b
    apply oddSpace_ext
    intro y c
    simp only [LinearMap.compl₁₂_apply, oddToTensor_vector, Submodule.subtype_apply]
    exact form_marked x y b c
  exact LinearMap.congr_fun (LinearMap.congr_fun he v) w

private theorem oddToTensor_injective : Function.Injective oddToTensor := by
  intro v w h
  have hz : oddToTensor (v - w) = 0 := by
    rw [LinearMap.map_sub (R := ℝ) (S := ℝ) (M := oddSpace) (M₂ := TensorTwo) oddToTensor, h, sub_self]
  have hf := oddToTensor_isometry (v-w) (v-w)
  simp only [hz, map_zero] at hf
  have hv : (v-w).val = 0 := by
    by_contra hn
    have hp := shortForm_pos sourceLatticeComparison (v-w).val hn
    linarith
  exact sub_eq_zero.mp (Subtype.ext hv)

private theorem oddToTensor_surjective : Function.Surjective oddToTensor := by
  have hq : oddToTensor.range.mkQ = 0 := by
    apply tensorTwo_ext
    intro x b
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨(zeroOdd x b).1, oddToTensor_vector x b⟩
  intro v
  have hv : oddToTensor.range.mkQ v = 0 := LinearMap.congr_fun hq v
  exact (Submodule.Quotient.mk_eq_zero _).mp hv

/-- The signed descent of 29.8, with the actual odd short span as source. -/
def oddComparison : oddSpace ≃ₗ[ℝ] TensorTwo :=
  LinearEquiv.ofBijective oddToTensor ⟨oddToTensor_injective, oddToTensor_surjective⟩

theorem oddComparison_vector (x : Omega) (b : ParkerLoop) :
    oddComparison (zeroOdd x b).1 = pointVector x ⊗ₜ[ℝ] delta2 b :=
  oddToTensor_vector x b

theorem oddComparison_isometry (v w : oddSpace) :
    tensorTwoForm (oddComparison v) (oddComparison w) =
      shortForm sourceLatticeComparison v.val w.val := oddToTensor_isometry v w

end Sporadic.Monster.Construction.NMonomial.ZeroAction
