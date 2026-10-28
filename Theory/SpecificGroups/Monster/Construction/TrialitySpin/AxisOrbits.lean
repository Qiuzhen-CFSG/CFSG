module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Generators

/-!
# Central involutions and the Parker axis orbits

The all-ones loop element and its negative are central involutions. Their
translations give the explicit `k1` action: a sign change on axis 1,
multiplication by `s` on axis 2, and multiplication by `sπ` on axis 3.
Thus the two-point `k1` orbits used for the first spin module have exactly
the representatives specified in the source. The sign involution `z1` acts
without fixed points on the union of axes 2 and 3.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6, pp. 62–63, and the
signed-basis construction preceding Lemma 27.3, p. 146. These are concrete
permutation facts; the real module and its action are separate constructions.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin

@[simp] theorem loopInverse_omega : loopInverse parkerOmega = parkerOmega := by
  apply (loopRight parkerOmega).injective
  change parkerLoopMultiply (loopInverse parkerOmega) parkerOmega =
    parkerLoopMultiply parkerOmega parkerOmega
  rw [loopInverse_mul, parkerOmega_square]
  rfl

theorem loopInverse_sign (s : ParkerBit) (x : ParkerLoop) :
    loopInverse (parkerSign s x) = parkerSign s (loopInverse x) := by
  apply Prod.ext
  · rfl
  · change (x.2 + s) + golayQuarterWeight x.1 = (x.2 + golayQuarterWeight x.1) + s
    ring

@[simp] theorem loopInverse_signOmega :
    loopInverse (parkerSign 1 parkerOmega) = parkerSign 1 parkerOmega := by
  rw [loopInverse_sign, loopInverse_omega]

theorem signOmega_commutes (x : ParkerLoop) :
    parkerLoopMultiply (parkerSign 1 parkerOmega) x =
      parkerLoopMultiply x (parkerSign 1 parkerOmega) := by
  rw [parkerLoopMultiply_sign_left, parkerOmega_commutes, parkerLoopMultiply_sign_right]

@[simp] theorem omega_sandwich (a : LoopZero) :
    rightZero parkerOmega (leftZero parkerOmega a) = a := by
  cases a with
  | none => rfl
  | some x =>
    simp only [leftZero_some, rightZero_some]
    apply congrArg some
    rw [parkerOmega_commutes]
    simpa only [loopInverse_omega] using loopInverse_mul_right parkerOmega x

@[simp] theorem signOmega_sandwich (a : LoopZero) :
    rightZero (parkerSign 1 parkerOmega) (leftZero (parkerSign 1 parkerOmega) a) = a := by
  cases a with
  | none => rfl
  | some x =>
    simp only [leftZero_some, rightZero_some]
    apply congrArg some
    rw [signOmega_commutes]
    simpa only [loopInverse_signOmega] using loopInverse_mul_right (parkerSign 1 parkerOmega) x

@[simp] theorem omega_commutes_zero (a : LoopZero) :
    leftZero parkerOmega a = rightZero parkerOmega a := by
  cases a with
  | none => rfl
  | some x => exact congrArg some (parkerOmega_commutes x)

@[simp] theorem signOmega_commutes_zero (a : LoopZero) :
    leftZero (parkerSign 1 parkerOmega) a = rightZero (parkerSign 1 parkerOmega) a := by
  cases a with
  | none => rfl
  | some x => exact congrArg some (signOmega_commutes x)

@[simp] theorem rightOmega_rightOmega (a : LoopZero) :
    rightZero parkerOmega (rightZero parkerOmega a) = a := by
  rw [← omega_commutes_zero a, omega_sandwich]

@[simp] theorem rightSignOmega_rightSignOmega (a : LoopZero) :
    rightZero (parkerSign 1 parkerOmega) (rightZero (parkerSign 1 parkerOmega) a) = a := by
  rw [← signOmega_commutes_zero a, signOmega_sandwich]

theorem omega_mixed_sandwich (a : LoopZero) :
    rightZero (parkerSign 1 parkerOmega) (leftZero parkerOmega a) = signZero a := by
  cases a with
  | none => rfl
  | some x =>
    simp only [leftZero_some, rightZero_some, signZero_some]
    apply congrArg some
    rw [parkerLoopMultiply_sign_right, parkerOmega_commutes]
    congr 1
    simpa only [loopInverse_omega] using loopInverse_mul_right parkerOmega x

theorem k1_apply (a b c : LoopZero) :
    k1.val (a, b, c) =
      (signZero a, rightZero parkerOmega b, rightZero (parkerSign 1 parkerOmega) c) := by
  change psi2 (parkerSign 1 parkerOmega) (psi3 parkerOmega (a, b, c)) = _
  simp only [psi2_apply, psi3_apply, loopInverse_omega, loopInverse_signOmega,
    omega_sandwich, omega_mixed_sandwich, signOmega_commutes_zero,
    rightSignOmega_rightSignOmega]

theorem k1_sq : k1 ^ 2 = 1 := by
  apply Subtype.ext
  ext ⟨a, b, c⟩ : 1
  change k1.val (k1.val (a, b, c)) = (a, b, c)
  simp only [k1_apply, signZero_signZero, rightOmega_rightOmega,
    rightSignOmega_rightSignOmega]

theorem k1_axis2 (b : ParkerLoop) :
    k1.val (axis2 b) = axis2 (parkerLoopMultiply b parkerOmega) := by
  simp [axis2, k1_apply]

theorem k1_axis3 (b : ParkerLoop) :
    k1.val (axis3 b) = axis3 (parkerLoopMultiply b (parkerSign 1 parkerOmega)) := by
  simp [axis3, k1_apply]

theorem z1_axis2 (b : ParkerLoop) : z1 (axis2 b) = axis2 (parkerSign 1 b) := by
  simp [axis2]

theorem z1_axis3 (b : ParkerLoop) : z1 (axis3 b) = axis3 (parkerSign 1 b) := by
  simp [axis3]

theorem parkerSign_one_ne (x : ParkerLoop) : parkerSign 1 x ≠ x := by
  intro h
  have hs : x.2 + 1 = x.2 := congrArg Prod.snd h
  simp at hs

theorem golayOne_ne_zero : golayOne ≠ 0 := by
  intro h
  have hc := congrArg (fun a : golay => a.val ((0, 0), 0)) h
  change (1 : Bit) = 0 at hc
  exact one_ne_zero hc

theorem mul_omega_ne (x : ParkerLoop) : parkerLoopMultiply x parkerOmega ≠ x := by
  intro h
  have hc : x.1 + golayOne = x.1 := congrArg Prod.fst h
  have hz : golayOne = 0 := add_left_cancel (hc.trans (add_zero _).symm)
  exact golayOne_ne_zero hz

theorem z1_fixedPointFree_on_A {a : Triple} (ha : a ∈ A) : z1 a ≠ a := by
  rcases ha with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rw [z1_axis2]
    intro he
    exact parkerSign_one_ne b (Option.some.inj (congrArg (fun t : Triple => t.2.1) he))
  · rw [z1_axis3]
    intro he
    exact parkerSign_one_ne b (Option.some.inj (congrArg (fun t : Triple => t.2.2) he))

end Sporadic.Monster.Construction.TrialitySpin
