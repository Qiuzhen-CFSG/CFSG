module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Decomposition

/-!
# The third signed module on the second Parker axis

The actual `k3` and `z3` permutations give two independent commuting
involutions on `A2`. Their signed orbit module has dimension 2048, a normalized
positive form, and the orbit-fixing criterion for every induced action.
Transport between such geometries is by the actual point equivalence.

Source: Aschbacher, *Sporadic Groups*, p. 146, the construction preceding
Lemma 27.3 and the module in clause (6). No subgroup-kernel identification
is asserted here.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin SignedModules
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Sporadic.Monster.Construction.TrialitySpin.SpinActions

/-- A pairing and an independent commuting sign change on actual points. -/
structure OrbitGeometry (X : Type*) where
  pairing : Pairing X
  signs : SignedSet X
  commute : ∀ x, signs.flip (pairing.flip x) = pairing.flip (signs.flip x)
  separate : ∀ x, signs.flip x ≠ pairing.flip x

namespace OrbitGeometry
variable {X Y : Type*} (S : OrbitGeometry X) (T : OrbitGeometry Y)
def signedOrbits : SignedSet S.pairing.Orbit :=
  S.pairing.signedQuotient S.signs S.commute S.separate
abbrev Space := S.signedOrbits.Space
def vector (x : X) : S.Space := S.signedOrbits.delta (S.pairing.orbit x)

@[simp] theorem vector_pair (x : X) : S.vector (S.pairing.flip x) = S.vector x := by
  simp only [vector, Pairing.orbit_flip]
@[simp] theorem vector_sign (x : X) : S.vector (S.signs.flip x) = -S.vector x :=
  S.signedOrbits.delta_flip (S.pairing.orbit x)

theorem transport_commute (e : X ≃ Y)
    (hk : ∀ x, e (S.pairing.flip x) = T.pairing.flip (e x))
    (hz : ∀ x, e (S.signs.flip x) = T.signs.flip (e x)) (a : S.pairing.Orbit) :
    S.pairing.transport T.pairing e hk (S.signedOrbits.flip a) =
      T.signedOrbits.flip (S.pairing.transport T.pairing e hk a) := by
  induction a using Quotient.inductionOn with
  | h x => exact congrArg T.pairing.orbit (hz x)

def transport (e : X ≃ Y)
    (hk : ∀ x, e (S.pairing.flip x) = T.pairing.flip (e x))
    (hz : ∀ x, e (S.signs.flip x) = T.signs.flip (e x)) : S.Space ≃ₗ[ℝ] T.Space :=
  S.signedOrbits.transport T.signedOrbits (S.pairing.transport T.pairing e hk)
    (S.transport_commute T e hk hz)

@[simp] theorem transport_vector (e : X ≃ Y)
    (hk : ∀ x, e (S.pairing.flip x) = T.pairing.flip (e x))
    (hz : ∀ x, e (S.signs.flip x) = T.signs.flip (e x)) (x : X) :
    S.transport T e hk hz (S.vector x) = T.vector (e x) :=
  S.signedOrbits.transport_delta T.signedOrbits _ _ _

theorem transport_isometry [Fintype S.pairing.Orbit] [Fintype T.pairing.Orbit]
    (e : X ≃ Y) (hk : ∀ x, e (S.pairing.flip x) = T.pairing.flip (e x))
    (hz : ∀ x, e (S.signs.flip x) = T.signs.flip (e x)) (v w : S.Space) :
    T.signedOrbits.form (S.transport T e hk hz v) (S.transport T e hk hz w) =
      S.signedOrbits.form v w := S.signedOrbits.transport_isometry T.signedOrbits _ _ v w

/-- Equality of linear maps can be checked on the actual signed vectors. -/
theorem vector_ext {M : Type*} [AddCommMonoid M] [Module ℝ M] [Finite X]
    (f g : S.Space →ₗ[ℝ] M) (h : ∀ x, f (S.vector x) = g (S.vector x)) : f = g := by
  apply S.signedOrbits.basis.ext
  intro a
  rw [SignedSet.basis_eq_delta]
  obtain ⟨x, hx⟩ := S.pairing.orbit_surjective a.out
  exact hx ▸ h x
end OrbitGeometry

def domainGeometry (D : SpinDomain) : OrbitGeometry D.points :=
  ⟨D.pairing, D.signs, D.signs_pairing_commute, D.signs_ne_pairing⟩

/-- The formula follows from the published product defining `k3`. -/
theorem k3_on_triple (a b c : LoopZero) :
    k3.val (a, b, c) =
      (rightZero parkerOmega a, rightZero (parkerSign 1 parkerOmega) b, signZero c) := by
  change psi1 (parkerSign 1 parkerOmega) (psi2 parkerOmega (a, b, c)) = _
  simp only [psi1_apply, psi2_apply, loopInverse_omega, loopInverse_signOmega,
    omega_sandwich, omega_mixed_sandwich, signOmega_commutes_zero,
    rightSignOmega_rightSignOmega]

theorem k3_on_axis2 (b : ParkerLoop) :
    k3.val (axis2 b) = axis2 (parkerLoopMultiply b (parkerSign 1 parkerOmega)) := by
  simp [axis2, k3_on_triple]

theorem z3_on_axis2 (b : ParkerLoop) : z3 (axis2 b) = axis2 (parkerSign 1 b) := by
  simp [axis2]

private theorem k3_involutive : Function.Involutive k3.val := by
  rintro ⟨a, b, c⟩
  simp only [k3_on_triple, rightOmega_rightOmega, rightSignOmega_rightSignOmega,
    signZero_signZero]

private theorem z3_involutive : Function.Involutive z3 := by
  intro a
  exact congrArg (fun e : Equiv.Perm Triple => e a) z3_sq

namespace B3Axis2

def pairing : Pairing A2 where
  flip :=
    { toFun a := ⟨k3.val a.val, by
        obtain ⟨b, hb⟩ := a.property
        exact ⟨_, (k3_on_axis2 b).symm.trans (congrArg k3.val hb)⟩⟩
      invFun a := ⟨k3.val a.val, by
        obtain ⟨b, hb⟩ := a.property
        exact ⟨_, (k3_on_axis2 b).symm.trans (congrArg k3.val hb)⟩⟩
      left_inv a := by exact Subtype.ext (k3_involutive a.val)
      right_inv a := by exact Subtype.ext (k3_involutive a.val) }
  involutive a := by exact Subtype.ext (k3_involutive a.val)

def signs : SignedSet A2 where
  flip :=
    { toFun a := ⟨z3 a.val, by
        obtain ⟨b, hb⟩ := a.property
        exact ⟨_, (z3_on_axis2 b).symm.trans (congrArg z3 hb)⟩⟩
      invFun a := ⟨z3 a.val, by
        obtain ⟨b, hb⟩ := a.property
        exact ⟨_, (z3_on_axis2 b).symm.trans (congrArg z3 hb)⟩⟩
      left_inv a := by exact Subtype.ext (z3_involutive a.val)
      right_inv a := by exact Subtype.ext (z3_involutive a.val) }
  involutive a := by exact Subtype.ext (z3_involutive a.val)
  fixedPointFree a := by
    obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
    intro h
    exact parkerSign_one_ne b (axis2_injective ((z3_on_axis2 b).symm.trans
      (congrArg Subtype.val h)))

@[simp] theorem pairing_axis (b : ParkerLoop) :
    pairing.flip (axis2Equiv b) = axis2Equiv (parkerLoopMultiply b (parkerSign 1 parkerOmega)) :=
  Subtype.ext (k3_on_axis2 b)
@[simp] theorem signs_axis (b : ParkerLoop) :
    signs.flip (axis2Equiv b) = axis2Equiv (parkerSign 1 b) := Subtype.ext (z3_on_axis2 b)

abbrev geometry : OrbitGeometry A2 where
  pairing := pairing
  signs := signs
  commute a := by
    obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
    simp only [pairing_axis, signs_axis, parkerLoopMultiply_sign_left]
  separate a := by
    obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
    rw [pairing_axis, signs_axis]
    intro h
    have hc := congrArg Prod.fst (axis2Equiv.injective h)
    change b.1 = b.1 + golayOne at hc
    exact golayOne_ne_zero (add_left_cancel ((add_zero b.1).trans hc).symm)

abbrev Space := geometry.Space
instance : Fintype pairing.Orbit := Fintype.ofFinite _
def form : LinearMap.BilinForm ℝ Space := geometry.signedOrbits.form
def delta (b : ParkerLoop) : Space := geometry.vector (axis2Equiv b)
def basis : Module.Basis geometry.signedOrbits.toPairing.Orbit ℝ Space :=
  geometry.signedOrbits.basis

@[simp] theorem delta_sign (b : ParkerLoop) : delta (parkerSign 1 b) = -delta b := by
  exact (congrArg geometry.vector (signs_axis b).symm).trans (geometry.vector_sign _)
@[simp] theorem delta_signOmega (b : ParkerLoop) :
    delta (parkerLoopMultiply b (parkerSign 1 parkerOmega)) = delta b := by
  exact (congrArg geometry.vector (pairing_axis b).symm).trans (geometry.vector_pair _)

theorem delta_eq_iff (b c : ParkerLoop) : delta b = delta c ↔
    b = c ∨ b = parkerLoopMultiply c (parkerSign 1 parkerOmega) := by
  change geometry.signedOrbits.delta _ = geometry.signedOrbits.delta _ ↔ _
  rw [geometry.signedOrbits.delta_injective.eq_iff, Pairing.orbit_eq, pairing_axis]
  simp only [axis2Equiv.injective.eq_iff]

theorem finrank : Module.finrank ℝ Space = 2048 := by
  have h₁ := geometry.signedOrbits.twice_finrank
  have h₂ := pairing.card_eq_twice (fun a => by
    obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
    rw [pairing_axis]
    intro h
    have hc := congrArg Prod.fst (axis2Equiv.injective h)
    change b.1 + golayOne = b.1 at hc
    exact golayOne_ne_zero (add_left_cancel (hc.trans (add_zero _).symm)))
  change Module.finrank ℝ Space * 2 = Nat.card pairing.Orbit at h₁
  rw [axis2_card] at h₂
  omega

theorem form_pos (v : Space) (hv : v ≠ 0) : 0 < form v v :=
  geometry.signedOrbits.form_pos v hv

theorem delta_norm (b : ParkerLoop) : form (delta b) (delta b) = 1 :=
  (geometry.signedOrbits.form_delta _ _).trans (geometry.signedOrbits.delta_self _)

theorem basis_orthonormal (a b : geometry.signedOrbits.toPairing.Orbit) :
    form (basis a) (basis b) = if a = b then 1 else 0 :=
  geometry.signedOrbits.basis_orthonormal a b

def restrictAction {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2) : G →* Equiv.Perm A2 where
  toFun g := (ρ g).subtypeEquiv (hA g)
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm Triple => e a.val) ρ.map_one
  map_mul' g h := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm Triple => e a.val) (ρ.map_mul g h)

/-- Restriction of an ambient action, using the actual `k3` and `z3`. -/
def inducedRepresentation {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) : Representation ℝ G Space :=
  pairing.signedRepresentation signs geometry.commute geometry.separate
    (restrictAction ρ hA)
    (fun g a => Subtype.ext (hk g a.val)) (fun g a => Subtype.ext (hz g a.val))

theorem inducedRepresentation_delta {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G) (b c : ParkerLoop)
    (hg : ρ g (axis2 b) = axis2 c) : inducedRepresentation ρ hA hk hz g (delta b) = delta c := by
  calc
    _ = geometry.vector (restrictAction ρ hA g (axis2Equiv b)) :=
      geometry.signedOrbits.representation_delta _ _ g _
    _ = delta c := congrArg geometry.vector (Subtype.ext hg)

theorem inducedRepresentation_kernel_iff {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple) (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G) :
    inducedRepresentation ρ hA hk hz g = 1 ↔
      ∀ a ∈ A2, ρ g a = a ∨ ρ g a = k3.val a := by
  refine (pairing.signedRepresentation_kernel_iff signs geometry.commute geometry.separate
    (restrictAction ρ hA) (fun g a => Subtype.ext (hk g a.val))
    (fun g a => Subtype.ext (hz g a.val)) g).trans ?_
  constructor
  · intro h a ha
    rcases h ⟨a, ha⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro h a
    rcases h a.val a.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem inducedRepresentation_isometry {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple) (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G) (v w : Space) :
    form (inducedRepresentation ρ hA hk hz g v)
      (inducedRepresentation ρ hA hk hz g w) = form v w :=
  geometry.signedOrbits.transport_isometry geometry.signedOrbits
    (pairing.orbitRepresentation (restrictAction ρ hA)
      (fun g a => Subtype.ext (hk g a.val)) g)
    (pairing.orbitRepresentation_commutes signs geometry.commute geometry.separate
      (restrictAction ρ hA) (fun g a => Subtype.ext (hk g a.val))
      (fun g a => Subtype.ext (hz g a.val)) g) v w

theorem inducedRepresentation_monomial {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple) (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G)
    (a : geometry.signedOrbits.toPairing.Orbit) :
    ∃ b, inducedRepresentation ρ hA hk hz g (basis a) = basis b ∨
      inducedRepresentation ρ hA hk hz g (basis a) = -basis b :=
  geometry.signedOrbits.representation_monomial _ _ g a
end B3Axis2
end Sporadic.Monster.Construction.TrialitySpin.SpinActions
namespace Sporadic.Monster.Construction.TrialitySpin
abbrev B3A2 := SpinActions.B3Axis2.Space
end Sporadic.Monster.Construction.TrialitySpin
