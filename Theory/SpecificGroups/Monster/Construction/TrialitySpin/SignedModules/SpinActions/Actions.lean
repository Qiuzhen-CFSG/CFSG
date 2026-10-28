module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Geometry
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.LoopFacts

/-!
# Linear maps induced by the Parker generators

The axis parametrizations transport the concrete loop permutations to the
actual orbit modules. Centrality of the all-ones loop element proves the
required normalization. In the odd case inversion followed by the standard
automorphism exchanges the central orbit relations; this gives maps
`B1A2 → B3A2` for `psiAut2` and `B1A2 → B1A3` for `psiAut1`.

All maps are linear equivalences preserving the normalized forms. Their
signed-vector formulas are Lemma 27.3(1)–(4) of Aschbacher, *Sporadic Groups*,
p. 146. Point-map comparisons retain the published triple permutations.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin.SpinActions
open SignedModules

/-- Coordinates for an actual signed axis, with its specified central orbit relation. -/
structure AxisRealization (X : Type*) where
  geometry : OrbitGeometry X
  param : ParkerLoop ≃ X
  twist : ParkerBit
  pairing_param : ∀ b, geometry.pairing.flip (param b) =
    param (parkerLoopMultiply b (parkerSign twist parkerOmega))
  signs_param : ∀ b, geometry.signs.flip (param b) = param (parkerSign 1 b)

namespace AxisRealization
variable {X Y : Type*} (U : AxisRealization X) (V : AxisRealization Y)

def pointMap (e : Equiv.Perm ParkerLoop) : X ≃ Y := U.param.symm.trans (e.trans V.param)
@[simp] theorem pointMap_param (e : Equiv.Perm ParkerLoop) (b : ParkerLoop) :
    U.pointMap V e (U.param b) = V.param (e b) := by simp [pointMap]

theorem pointMap_pair (e : Equiv.Perm ParkerLoop)
    (hk : ∀ b, e (parkerLoopMultiply b (parkerSign U.twist parkerOmega)) =
      parkerLoopMultiply (e b) (parkerSign V.twist parkerOmega)) (x : X) :
    U.pointMap V e (U.geometry.pairing.flip x) =
      V.geometry.pairing.flip (U.pointMap V e x) := by
  obtain ⟨b, rfl⟩ := U.param.surjective x
  rw [U.pairing_param, pointMap_param, pointMap_param, V.pairing_param, hk]

theorem pointMap_sign (e : Equiv.Perm ParkerLoop)
    (hz : ∀ b, e (parkerSign 1 b) = parkerSign 1 (e b)) (x : X) :
    U.pointMap V e (U.geometry.signs.flip x) =
      V.geometry.signs.flip (U.pointMap V e x) := by
  obtain ⟨b, rfl⟩ := U.param.surjective x
  rw [U.signs_param, pointMap_param, pointMap_param, V.signs_param, hz]

def transport (e : Equiv.Perm ParkerLoop)
    (hk : ∀ b, e (parkerLoopMultiply b (parkerSign U.twist parkerOmega)) =
      parkerLoopMultiply (e b) (parkerSign V.twist parkerOmega))
    (hz : ∀ b, e (parkerSign 1 b) = parkerSign 1 (e b)) :
    U.geometry.Space ≃ₗ[ℝ] V.geometry.Space :=
  U.geometry.transport V.geometry (U.pointMap V e)
    (U.pointMap_pair V e hk) (U.pointMap_sign V e hz)

@[simp] theorem transport_vector (e : Equiv.Perm ParkerLoop)
    (hk : ∀ b, e (parkerLoopMultiply b (parkerSign U.twist parkerOmega)) =
      parkerLoopMultiply (e b) (parkerSign V.twist parkerOmega))
    (hz : ∀ b, e (parkerSign 1 b) = parkerSign 1 (e b)) (b : ParkerLoop) :
    U.transport V e hk hz (U.geometry.vector (U.param b)) =
      V.geometry.vector (V.param (e b)) := by
  exact (U.geometry.transport_vector V.geometry _ _ _ _).trans
    (congrArg V.geometry.vector (U.pointMap_param V e b))

theorem transport_isometry [Fintype U.geometry.pairing.Orbit]
    [Fintype V.geometry.pairing.Orbit] (e : Equiv.Perm ParkerLoop)
    (hk : ∀ b, e (parkerLoopMultiply b (parkerSign U.twist parkerOmega)) =
      parkerLoopMultiply (e b) (parkerSign V.twist parkerOmega))
    (hz : ∀ b, e (parkerSign 1 b) = parkerSign 1 (e b)) (v w : U.geometry.Space) :
    V.geometry.signedOrbits.form (U.transport V e hk hz v) (U.transport V e hk hz w) =
      U.geometry.signedOrbits.form v w :=
  U.geometry.transport_isometry V.geometry _ _ _ v w

def leftAction (d : ParkerLoop) : U.geometry.Space ≃ₗ[ℝ] U.geometry.Space :=
  U.transport U (loopLeft d) (fun b => left_twist d b U.twist)
    (fun b => parkerLoopMultiply_sign_right 1 d b)

def rightAction (d : ParkerLoop) : U.geometry.Space ≃ₗ[ℝ] U.geometry.Space :=
  U.transport U (loopRight d) (fun b => right_twist d b U.twist)
    (fun b => parkerLoopMultiply_sign_left 1 b d)

def sandwichAction (d : ParkerLoop) : U.geometry.Space ≃ₗ[ℝ] U.geometry.Space :=
  (U.leftAction (loopInverse d)).trans (U.rightAction (loopInverse d))

@[simp] theorem leftAction_vector (d b : ParkerLoop) :
    U.leftAction d (U.geometry.vector (U.param b)) =
      U.geometry.vector (U.param (parkerLoopMultiply d b)) := U.transport_vector U _ _ _ b
@[simp] theorem rightAction_vector (d b : ParkerLoop) :
    U.rightAction d (U.geometry.vector (U.param b)) =
      U.geometry.vector (U.param (parkerLoopMultiply b d)) := U.transport_vector U _ _ _ b

theorem sandwichAction_vector (d b : ParkerLoop) :
    U.sandwichAction d (U.geometry.vector (U.param b)) =
      U.geometry.vector (U.param
        (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b)) := by
  simp only [sandwichAction, LinearEquiv.trans_apply, leftAction_vector,
    rightAction_vector, inverse_sandwich]

def evenAction (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega = parkerOmega) : U.geometry.Space ≃ₗ[ℝ] U.geometry.Space :=
  U.transport U e
    (fun b => by simpa only [parkerSign_zero, add_zero] using
      standard_twist e he 0 (by simpa only [parkerSign_zero] using hε) b U.twist)
    (fun b => standard_sign e he 1 b)

def oddAction (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (hUV : V.twist = U.twist + 1) :
    U.geometry.Space ≃ₗ[ℝ] V.geometry.Space :=
  U.transport V (loopInverseEquiv.trans e)
    (fun b => by
      change e (loopInverse (parkerLoopMultiply b (parkerSign U.twist parkerOmega))) = _
      rw [inverse_twist, standard_twist e he 1 (standard_omega_odd e he hε), ← hUV]
      rfl)
    (fun b => by
      change e (loopInverse (parkerSign 1 b)) = parkerSign 1 (e (loopInverse b))
      rw [loopInverse_sign, standard_sign e he])

@[simp] theorem evenAction_vector (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega = parkerOmega) (b : ParkerLoop) :
    U.evenAction e he hε (U.geometry.vector (U.param b)) =
      U.geometry.vector (U.param (e b)) := U.transport_vector U _ _ _ b

@[simp] theorem oddAction_vector (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (hUV : V.twist = U.twist + 1) (b : ParkerLoop) :
    U.oddAction V e he hε hUV (U.geometry.vector (U.param b)) =
      V.geometry.vector (V.param (parkerSign (golayQuarterWeight b.1) (e b))) := by
  calc
    _ = V.geometry.vector (V.param (e (loopInverse b))) := U.transport_vector V _ _ _ b
    _ = _ := by rw [loopInverse, standard_sign e he]

theorem leftAction_isometry [Fintype U.geometry.pairing.Orbit] (d : ParkerLoop)
    (v w : U.geometry.Space) : U.geometry.signedOrbits.form
      (U.leftAction d v) (U.leftAction d w) = U.geometry.signedOrbits.form v w :=
  U.transport_isometry U _ _ _ v w

theorem rightAction_isometry [Fintype U.geometry.pairing.Orbit] (d : ParkerLoop)
    (v w : U.geometry.Space) : U.geometry.signedOrbits.form
      (U.rightAction d v) (U.rightAction d w) = U.geometry.signedOrbits.form v w :=
  U.transport_isometry U _ _ _ v w

theorem sandwichAction_isometry [Fintype U.geometry.pairing.Orbit] (d : ParkerLoop)
    (v w : U.geometry.Space) : U.geometry.signedOrbits.form
      (U.sandwichAction d v) (U.sandwichAction d w) = U.geometry.signedOrbits.form v w :=
  (U.rightAction_isometry (loopInverse d) (U.leftAction (loopInverse d) v)
    (U.leftAction (loopInverse d) w)).trans (U.leftAction_isometry (loopInverse d) v w)

theorem evenAction_isometry [Fintype U.geometry.pairing.Orbit]
    (e : Equiv.Perm ParkerLoop) (he : IsStandard e) (hε : e parkerOmega = parkerOmega)
    (v w : U.geometry.Space) : U.geometry.signedOrbits.form
      (U.evenAction e he hε v) (U.evenAction e he hε w) = U.geometry.signedOrbits.form v w :=
  U.transport_isometry U _ _ _ v w

theorem oddAction_isometry [Fintype U.geometry.pairing.Orbit]
    [Fintype V.geometry.pairing.Orbit] (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (hUV : V.twist = U.twist + 1)
    (v w : U.geometry.Space) : V.geometry.signedOrbits.form
      (U.oddAction V e he hε hUV v) (U.oddAction V e he hε hUV w) =
      U.geometry.signedOrbits.form v w := U.transport_isometry V _ _ _ v w

end AxisRealization

abbrev firstSecond : AxisRealization A2 where
  geometry := domainGeometry secondAxisDomain
  param := axis2Equiv
  twist := 0
  pairing_param b := by
    change secondAxisDomain.pairing.flip (axis2Equiv b) =
      axis2Equiv (parkerLoopMultiply b (parkerSign 0 parkerOmega))
    rw [parkerSign_zero]
    exact Subtype.ext (k1_axis2 b)
  signs_param b := Subtype.ext (z1_axis2 b)

abbrev firstThird : AxisRealization A3 where
  geometry := domainGeometry thirdAxisDomain
  param := axis3Equiv
  twist := 1
  pairing_param b := Subtype.ext (k1_axis3 b)
  signs_param b := Subtype.ext (z1_axis3 b)

abbrev thirdSecond : AxisRealization A2 where
  geometry := B3Axis2.geometry
  param := axis2Equiv
  twist := 1
  pairing_param := B3Axis2.pairing_axis
  signs_param := B3Axis2.signs_axis

/-- The linear action of `psi1(d)` on the first signed second axis. -/
def psi1B1 (d : ParkerLoop) : B1A2 ≃ₗ[ℝ] B1A2 := firstSecond.leftAction d
/-- The linear action of `psi2(d)` on the first signed second axis. -/
def psi2B1 (d : ParkerLoop) : B1A2 ≃ₗ[ℝ] B1A2 := firstSecond.sandwichAction d
def psi3B1 (d : ParkerLoop) : B1A2 ≃ₗ[ℝ] B1A2 := firstSecond.rightAction d

def psi1B3 (d : ParkerLoop) : B3A2 ≃ₗ[ℝ] B3A2 := thirdSecond.leftAction d
def psi2B3 (d : ParkerLoop) : B3A2 ≃ₗ[ℝ] B3A2 := thirdSecond.sandwichAction d
def psi3B3 (d : ParkerLoop) : B3A2 ≃ₗ[ℝ] B3A2 := thirdSecond.rightAction d

/-- Lemma 27.3(1). The coordinate permutation is the published `psi1`. -/
theorem psi1B1_delta (d b : ParkerLoop) :
    psi1B1 d (delta2 b) = delta2 (parkerLoopMultiply d b) := firstSecond.leftAction_vector d b

/-- Lemma 27.3(2), with both the square and commutator signs. -/
theorem psi2B1_delta (d b : ParkerLoop) : psi2B1 d (delta2 b) =
    delta2 (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b) :=
  firstSecond.sandwichAction_vector d b

theorem psi3B1_delta (d b : ParkerLoop) :
    psi3B1 d (delta2 b) = delta2 (parkerLoopMultiply b d) := firstSecond.rightAction_vector d b

theorem psi1B3_delta (d b : ParkerLoop) :
    psi1B3 d (B3Axis2.delta b) = B3Axis2.delta (parkerLoopMultiply d b) :=
  thirdSecond.leftAction_vector d b

theorem psi2B3_delta (d b : ParkerLoop) : psi2B3 d (B3Axis2.delta b) =
    B3Axis2.delta (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b) :=
  thirdSecond.sandwichAction_vector d b

def psiAut2Even (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega = parkerOmega) : B1A2 ≃ₗ[ℝ] B1A2 := firstSecond.evenAction e he hε

/-- Odd `psiAut2` transports the second axis from `k1` orbits to `k3` orbits. -/
def psiAut2Odd (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) : B1A2 ≃ₗ[ℝ] B3A2 :=
  firstSecond.oddAction thirdSecond e he hε rfl

/-- Odd `psiAut1` exchanges the two halves of the first spin space. -/
def psiAut1Odd (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) : B1A2 ≃ₗ[ℝ] B1A3 :=
  firstSecond.oddAction firstThird e he hε rfl

def psiAut1OddBack (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) : B1A3 ≃ₗ[ℝ] B1A2 :=
  firstThird.oddAction firstSecond e he hε rfl

/-- Lemma 27.3(3). -/
theorem psiAut2Even_delta (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega = parkerOmega) (b : ParkerLoop) :
    psiAut2Even e he hε (delta2 b) = delta2 (e b) := firstSecond.evenAction_vector e he hε b

/-- Lemma 27.3(4), with its `B3(A2)` target made explicit. -/
theorem psiAut2Odd_delta (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut2Odd e he hε (delta2 b) =
      B3Axis2.delta (parkerSign (golayQuarterWeight b.1) (e b)) :=
  firstSecond.oddAction_vector thirdSecond e he hε rfl b

/-- Lemma 27.3(4), for the exchange of the two spin halves. -/
theorem psiAut1Odd_delta (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1Odd e he hε (delta2 b) =
      delta3 (parkerSign (golayQuarterWeight b.1) (e b)) :=
  firstSecond.oddAction_vector firstThird e he hε rfl b

theorem psiAut1OddBack_delta (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1OddBack e he hε (delta3 b) =
      delta2 (parkerSign (golayQuarterWeight b.1) (e b)) :=
  firstThird.oddAction_vector firstSecond e he hε rfl b

/-- The point map inducing the odd axis-2 transport is exactly `psiAut2`. -/
theorem psiAut2Odd_point (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) (a : A2) :
    (firstSecond.pointMap thirdSecond (loopInverseEquiv.trans e) a).val = psiAut2 e a.val := by
  obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
  rw [AxisRealization.pointMap_param]
  change axis2 (e (loopInverse b)) = psiAut2 e (axis2 b)
  rw [loopInverse, standard_sign e he]
  exact (psiAut2_odd_axis e he ho b).symm

/-- The point map inducing the exchange of halves is exactly `psiAut1`. -/
theorem psiAut1Odd_point (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (ho : e parkerOmega ≠ parkerOmega) (a : A2) :
    (firstSecond.pointMap firstThird (loopInverseEquiv.trans e) a).val = psiAut1 e a.val := by
  obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
  rw [AxisRealization.pointMap_param]
  change axis3 (e (loopInverse b)) = psiAut1 e (axis2 b)
  rw [loopInverse, standard_sign e he]
  exact (psiAut1_odd_axis e he ho b).symm

end Sporadic.Monster.Construction.TrialitySpin.SpinActions
