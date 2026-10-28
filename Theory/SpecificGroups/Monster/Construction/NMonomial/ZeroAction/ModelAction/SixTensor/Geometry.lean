module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.ModelAction.TransportData
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Actions
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Six signed orbit modules on the genuine Parker axes

For an ordered pair `(j,i)` of distinct zero-based axes, the spin factor is the
signed orbit module on the actual ith axis, with pairing `k_j` and sign `z_j`.
The positive cyclic pairs use multiplication by Omega; the reverse pairs use
signed Omega. The literal permutation formulas below certify those conventions.
Marked isomorphisms identify the three previously published spin modules, and
the marked natural-by-spin vectors span every tensor factor.

Source: Aschbacher, *Sporadic Groups*, Sections 14 and 27 (printed pp. 58–63,
146–147), and the six oriented factors underlying 29.7 (printed pp. 156–157).
-/

@[expose] public section
noncomputable section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin
open SignedModules SpinActions
open scoped TensorProduct
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor

/-- Ordered distinct axes: natural factor first, Parker axis second. -/
def Slot := {p : Natural.Axis × Natural.Axis // p.1 ≠ p.2}
instance : Fintype Slot := inferInstanceAs (Fintype {p : Natural.Axis × Natural.Axis // p.1 ≠ p.2})
instance : DecidableEq Slot := inferInstanceAs (DecidableEq {p : Natural.Axis × Natural.Axis // p.1 ≠ p.2})

def Slot.natural (p : Slot) : Natural.Axis := p.val.1
def Slot.spin (p : Slot) : Natural.Axis := p.val.2

def twist (p : Slot) : ParkerBit := if p.spin = p.natural + 1 then 0 else 1

abbrev Points (i : Natural.Axis) := Set.range (Natural.point i)
def param (i : Natural.Axis) : ParkerLoop ≃ Points i :=
  Equiv.ofInjective (Natural.point i) (Natural.point_injective i)

@[simp] theorem param_val (i : Natural.Axis) (b : ParkerLoop) :
    (param i b).val = Natural.point i b := rfl

private theorem twist_twice (t : ParkerBit) (b : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply b (parkerSign t parkerOmega))
      (parkerSign t parkerOmega) = b := by
  simpa only [loopInverse_sign, loopInverse_omega] using
    loopInverse_mul_right (parkerSign t parkerOmega) b

/-- The central orbit involution on the actual axis. -/
def pairing (i : Natural.Axis) (t : ParkerBit) : Pairing (Points i) where
  flip := (param i).symm.trans ((loopRight (parkerSign t parkerOmega)).trans (param i))
  involutive a := by
    obtain ⟨b,rfl⟩ := (param i).surjective a
    change param i (parkerLoopMultiply ((param i).symm
      (param i (parkerLoopMultiply ((param i).symm (param i b)) (parkerSign t parkerOmega))))
      (parkerSign t parkerOmega)) = param i b
    simp only [Equiv.symm_apply_apply, twist_twice]

@[simp] theorem pairing_param (i : Natural.Axis) (t : ParkerBit) (b : ParkerLoop) :
    (pairing i t).flip (param i b) =
      param i (parkerLoopMultiply b (parkerSign t parkerOmega)) := by
  simp [pairing, loopRight]

/-- The central sign on the actual axis. -/
def signs (i : Natural.Axis) : SignedSet (Points i) where
  flip := (param i).symm.trans ((loopLeft loopPi).trans (param i))
  involutive a := by
    obtain ⟨b,rfl⟩ := (param i).surjective a
    simp [loopLeft, loopPi_mul, parkerSign_add]
  fixedPointFree a := by
    obtain ⟨b,rfl⟩ := (param i).surjective a
    intro h
    apply parkerSign_one_ne b
    apply (param i).injective
    simpa [loopLeft, loopPi_mul] using h

@[simp] theorem signs_param (i : Natural.Axis) (b : ParkerLoop) :
    (signs i).flip (param i b) = param i (parkerSign 1 b) := by
  simp [signs, loopLeft, loopPi_mul]

/-- Uniform realization; its twist is checked against the literal involutions below. -/
def realization (i : Natural.Axis) (t : ParkerBit) : AxisRealization (Points i) where
  geometry :=
    { pairing := pairing i t
      signs := signs i
      commute a := by
        obtain ⟨b,rfl⟩ := (param i).surjective a
        simp only [pairing_param, signs_param, parkerLoopMultiply_sign_left]
      separate a := by
        obtain ⟨b,rfl⟩ := (param i).surjective a
        rw [signs_param, pairing_param]
        intro h
        have hc := congrArg Prod.fst ((param i).injective h)
        change b.1 = b.1 + golayOne at hc
        exact golayOne_ne_zero (add_left_cancel ((add_zero b.1).trans hc).symm) }
  param := param i
  twist := t
  pairing_param := pairing_param i t
  signs_param := signs_param i

abbrev geometry (p : Slot) : OrbitGeometry (Points p.spin) :=
  (realization p.spin (twist p)).geometry
abbrev Spin (p : Slot) := (geometry p).Space
abbrev Tensor (p : Slot) := Natural.Space p.natural ⊗[ℝ] Spin p

def delta (p : Slot) (b : ParkerLoop) : Spin p := (geometry p).vector (param p.spin b)
def marked (p : Slot) (x : Omega) (b : ParkerLoop) : Tensor p :=
  Natural.L p.natural 1 x ⊗ₜ[ℝ] delta p b

instance (p : Slot) : Fintype (geometry p).pairing.Orbit := Fintype.ofFinite _

def spinForm (p : Slot) : LinearMap.BilinForm ℝ (Spin p) := (geometry p).signedOrbits.form

@[simp] theorem delta_pair (p : Slot) (b : ParkerLoop) :
    delta p (parkerLoopMultiply b (parkerSign (twist p) parkerOmega)) = delta p b := by
  exact (congrArg (geometry p).vector (pairing_param p.spin (twist p) b).symm).trans
    ((geometry p).vector_pair _)

@[simp] theorem delta_sign (p : Slot) (b : ParkerLoop) :
    delta p (parkerSign 1 b) = -delta p b := by
  exact (congrArg (geometry p).vector (signs_param p.spin b).symm).trans
    ((geometry p).vector_sign _)

theorem k2_apply (a b c : LoopZero) :
    k2.val (a,b,c) =
      (rightZero (parkerSign 1 parkerOmega) a, signZero b, rightZero parkerOmega c) := by
  change psi3 (parkerSign 1 parkerOmega) (psi1 parkerOmega (a,b,c)) = _
  simp only [psi1_apply, psi3_apply, loopInverse_omega, loopInverse_signOmega,
    omega_sandwich, omega_mixed_sandwich, signOmega_commutes_zero,
    rightSignOmega_rightSignOmega]

/-- The six pairings are the specified `k_j` restrictions, with their actual signs. -/
theorem axisK_point (p : Slot) (b : ParkerLoop) :
    (axisK p.natural).val (Natural.point p.spin b) =
      Natural.point p.spin (parkerLoopMultiply b (parkerSign (twist p) parkerOmega)) := by
  rcases p with ⟨⟨j,i⟩,h⟩
  fin_cases j <;> fin_cases i
  all_goals try exact False.elim (h rfl)
  all_goals simp [Slot.natural, Slot.spin, twist, axisK, Natural.point, k1_apply,
    k2_apply, k3_on_triple, axis1, axis2, axis3]

/-- The six sign changes are the specified `z_j` restrictions. -/
theorem axisZ_point (p : Slot) (b : ParkerLoop) :
    (axisZ p.natural).val (Natural.point p.spin b) =
      Natural.point p.spin (parkerSign 1 b) := by
  rcases p with ⟨⟨j,i⟩,h⟩
  fin_cases j <;> fin_cases i
  all_goals try exact False.elim (h rfl)
  all_goals simp [Slot.natural, Slot.spin, axisZ, Natural.point, z1N, z2N, z3N,
    psi1N, psi2N, psi3N, axis1, axis2, axis3]

theorem pairing_val (p : Slot) (a : Points p.spin) :
    ((geometry p).pairing.flip a).val = (axisK p.natural).val a.val := by
  obtain ⟨b,rfl⟩ := (param p.spin).surjective a
  rw [show (geometry p).pairing = pairing p.spin (twist p) from rfl, pairing_param]
  exact (axisK_point p b).symm

theorem signs_val (p : Slot) (a : Points p.spin) :
    ((geometry p).signs.flip a).val = (axisZ p.natural).val a.val := by
  obtain ⟨b,rfl⟩ := (param p.spin).surjective a
  rw [show (geometry p).signs = signs p.spin from rfl, signs_param]
  exact (axisZ_point p b).symm

def slot01 : Slot := ⟨(0,1), by decide⟩
def slot21 : Slot := ⟨(2,1), by decide⟩
def slot02 : Slot := ⟨(0,2), by decide⟩
def slot20 : Slot := ⟨(2,0), by decide⟩
def slot12 : Slot := ⟨(1,2), by decide⟩
def slot10 : Slot := ⟨(1,0), by decide⟩

/-- A marked comparison requires the same orbit relation, not just equal dimensions. -/
def spinComparison {X : Type*} (p : Slot) (U : AxisRealization X) (h : twist p = U.twist) :
    Spin p ≃ₗ[ℝ] U.geometry.Space :=
  (realization p.spin (twist p)).transport U (Equiv.refl _)
    (fun b => by change parkerLoopMultiply b (parkerSign (twist p) parkerOmega) =
      parkerLoopMultiply b (parkerSign U.twist parkerOmega); rw [h]) (fun _ => rfl)

theorem spinComparison_delta {X : Type*} (p : Slot) (U : AxisRealization X)
    (h : twist p = U.twist) (b : ParkerLoop) :
    spinComparison p U h (delta p b) = U.geometry.vector (U.param b) :=
  (realization p.spin (twist p)).transport_vector U _ _ _ b

theorem spinComparison_isometry {X : Type*} (p : Slot) (U : AxisRealization X)
    [Fintype U.geometry.pairing.Orbit] (h : twist p = U.twist) (v w : Spin p) :
    U.geometry.signedOrbits.form (spinComparison p U h v) (spinComparison p U h w) =
      spinForm p v w := (realization p.spin (twist p)).transport_isometry U _ _ _ v w

def toB1A2 : Spin slot01 ≃ₗ[ℝ] B1A2 := spinComparison slot01 firstSecond rfl
def toB3A2 : Spin slot21 ≃ₗ[ℝ] B3A2 := spinComparison slot21 thirdSecond rfl
def toB1A3 : Spin slot02 ≃ₗ[ℝ] B1A3 := spinComparison slot02 firstThird rfl

@[simp] theorem toB1A2_delta (b : ParkerLoop) : toB1A2 (delta slot01 b) = delta2 b :=
  spinComparison_delta slot01 firstSecond rfl b
@[simp] theorem toB3A2_delta (b : ParkerLoop) : toB3A2 (delta slot21 b) = B3Axis2.delta b :=
  spinComparison_delta slot21 thirdSecond rfl b
@[simp] theorem toB1A3_delta (b : ParkerLoop) : toB1A3 (delta slot02 b) = delta3 b :=
  spinComparison_delta slot02 firstThird rfl b

/-- The signed Parker vectors span each orbit module. -/
theorem delta_ext {M : Type*} [AddCommMonoid M] [Module ℝ M] (p : Slot)
    (f g : Spin p →ₗ[ℝ] M) (h : ∀ b, f (delta p b) = g (delta p b)) : f = g := by
  apply (geometry p).vector_ext
  intro a
  obtain ⟨b,rfl⟩ := (param p.spin).surjective a
  exact h b

/-- The marked natural-by-Parker vectors span each tensor factor. -/
theorem marked_ext {M : Type*} [AddCommMonoid M] [Module ℝ M] (p : Slot)
    (f g : Tensor p →ₗ[ℝ] M) (h : ∀ x b, f (marked p x b) = g (marked p x b)) : f = g := by
  apply TensorProduct.ext
  apply (Natural.basis p.natural).ext
  intro x
  apply delta_ext p
  intro b
  change f (Natural.basis p.natural x ⊗ₜ[ℝ] delta p b) =
    g (Natural.basis p.natural x ⊗ₜ[ℝ] delta p b)
  rw [Natural.basis_eq_L]
  exact h x b

end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction.SixTensor
