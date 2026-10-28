module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.AxisOrbits
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Core
public import Mathlib.Logic.Equiv.Set

/-!
# The real signed Parker-axis spaces

The points used here are subtypes of the published coordinate axes `A2`,
`A3`, and `A = A2 ∪ A3`. First quotient by the actual `k1` permutation,
then take real functions anti-invariant under the actual `z1` permutation.
Both involutions act freely, and a sign image never belongs to its original
`k1` orbit. Consequently the half-spaces have dimension 2048 and the space
on both axes has dimension 4096.

Signed delta functions give the source relations and the unit normalization.
The general signed-set construction supplies orthonormal bases and positive
definite invariant forms. Ambient permutations preserving the domain and
commuting with `k1` and `z1` induce concrete monomial representations. Their
kernels fix every `k1` orbit, and `z1` acts as minus identity.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and Exercise 4.3;
the spaces preceding Lemma 27.3, printed pp. 146–147. Restricting the actions
to the source groups requires the stated permutation normalization hypotheses;
no group-theoretic kernel or irreducibility conclusion is assumed here.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open Atlas.Fischer Atlas.Codes
namespace Sporadic.Monster.Construction.TrialitySpin
open SignedModules

/-- The axis parametrizations are genuine bijections onto the published axes. -/
theorem axis2_injective : Function.Injective axis2 := by
  intro x y h
  exact Option.some.inj (congrArg (fun t : Triple => t.2.1) h)

theorem axis3_injective : Function.Injective axis3 := by
  intro x y h
  exact Option.some.inj (congrArg (fun t : Triple => t.2.2) h)

def axis2Equiv : ParkerLoop ≃ A2 := Equiv.ofInjective axis2 axis2_injective
def axis3Equiv : ParkerLoop ≃ A3 := Equiv.ofInjective axis3 axis3_injective

theorem axes_disjoint : Disjoint A2 A3 := by
  rw [Set.disjoint_left]
  rintro a ⟨x, rfl⟩ ⟨y, h⟩
  have he := congrArg (fun t : Triple => t.2.1) h
  simp [axis2, axis3] at he

theorem axis2_card : Nat.card A2 = 8192 :=
  (Nat.card_congr axis2Equiv).symm.trans parkerLoop_card

theorem axis3_card : Nat.card A3 = 8192 :=
  (Nat.card_congr axis3Equiv).symm.trans parkerLoop_card

theorem spinAxes_card : Nat.card A = 16384 := by
  have h := Nat.card_congr (Equiv.Set.union axes_disjoint)
  rw [Nat.card_sum, axis2_card, axis3_card] at h
  exact h

private theorem signZero_right (d : ParkerLoop) (x : LoopZero) :
    signZero (rightZero d x) = rightZero d (signZero x) := by
  cases x with
  | none => rfl
  | some x => simp [parkerLoopMultiply_sign_left]

theorem z1_k1_commute (a : Triple) : z1 (k1.val a) = k1.val (z1 a) := by
  rcases a with ⟨a, b, c⟩
  simp only [k1_apply, z1_apply, signZero_right]

theorem k1_involutive : Function.Involutive k1.val := by
  intro a
  have h := congrArg (fun g : N => g.val a) k1_sq
  exact h

theorem z1_involutive : Function.Involutive z1 := by
  intro a
  have h := congrArg (fun g : Equiv.Perm Triple => g a) z1_sq
  exact h

private theorem mul_omega_code_ne (x y : ParkerLoop) (hy : y.1 = x.1)
    (d : ParkerLoop) (hd : d.1 = golayOne) : parkerLoopMultiply x d ≠ y := by
  intro h
  have hc' : x.1 + d.1 = y.1 := congrArg Prod.fst h
  have hc : x.1 + golayOne = x.1 := by
    simpa only [hd, hy] using hc'
  exact golayOne_ne_zero (add_left_cancel (hc.trans (add_zero _).symm))

theorem k1_fixedPointFree_on_A {a : Triple} (ha : a ∈ A) : k1.val a ≠ a := by
  rcases ha with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [k1_axis2]
    exact fun h => mul_omega_ne x (axis2_injective h)
  · rw [k1_axis3]
    exact fun h => mul_omega_code_ne x x rfl (parkerSign 1 parkerOmega) rfl
      (axis3_injective h)

theorem z1_ne_k1_on_A {a : Triple} (ha : a ∈ A) : z1 a ≠ k1.val a := by
  rcases ha with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [z1_axis2, k1_axis2]
    exact fun h => mul_omega_code_ne x (parkerSign 1 x) rfl parkerOmega rfl
      (axis2_injective h.symm)
  · rw [z1_axis3, k1_axis3]
    exact fun h => mul_omega_code_ne x (parkerSign 1 x) rfl
      (parkerSign 1 parkerOmega) rfl (axis3_injective h.symm)

/-- An actual subset of the two axes, stable under the two specified permutations. -/
structure SpinDomain where
  points : Set Triple
  subset_axes : points ⊆ A
  k_mem : ∀ a ∈ points, k1.val a ∈ points
  z_mem : ∀ a ∈ points, z1 a ∈ points

/-- The first half of the spin space, supported on the actual second axis. -/
def secondAxisDomain : SpinDomain where
  points := A2
  subset_axes := Set.subset_union_left
  k_mem := by rintro a ⟨b, rfl⟩; exact ⟨_, (k1_axis2 b).symm⟩
  z_mem := by rintro a ⟨b, rfl⟩; exact ⟨_, (z1_axis2 b).symm⟩

/-- The other half, whose orbit relation uses `sπ` rather than `s`. -/
def thirdAxisDomain : SpinDomain where
  points := A3
  subset_axes := Set.subset_union_right
  k_mem := by rintro a ⟨b, rfl⟩; exact ⟨_, (k1_axis3 b).symm⟩
  z_mem := by rintro a ⟨b, rfl⟩; exact ⟨_, (z1_axis3 b).symm⟩

/-- Both axes together; odd first automorphisms may interchange its halves. -/
def bothAxesDomain : SpinDomain where
  points := A
  subset_axes := fun _ h => h
  k_mem := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (secondAxisDomain.k_mem a ha)
    · exact Or.inr (thirdAxisDomain.k_mem a ha)
  z_mem := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (secondAxisDomain.z_mem a ha)
    · exact Or.inr (thirdAxisDomain.z_mem a ha)

namespace SpinDomain
variable (D : SpinDomain)

/-- Restriction of the concrete permutation `k1`, with no abstract orbit labels. -/
def pairing : Pairing D.points where
  flip :=
    { toFun a := ⟨k1.val a.val, D.k_mem _ a.property⟩
      invFun a := ⟨k1.val a.val, D.k_mem _ a.property⟩
      left_inv a := Subtype.ext (k1_involutive a.val)
      right_inv a := Subtype.ext (k1_involutive a.val) }
  involutive a := Subtype.ext (k1_involutive a.val)

/-- Restriction of the concrete sign change `z1`. -/
def signs : SignedSet D.points where
  flip :=
    { toFun a := ⟨z1 a.val, D.z_mem _ a.property⟩
      invFun a := ⟨z1 a.val, D.z_mem _ a.property⟩
      left_inv a := Subtype.ext (z1_involutive a.val)
      right_inv a := Subtype.ext (z1_involutive a.val) }
  involutive a := Subtype.ext (z1_involutive a.val)
  fixedPointFree a h := z1_fixedPointFree_on_A (D.subset_axes a.property)
    (congrArg Subtype.val h)

theorem signs_pairing_commute (a : D.points) :
    D.signs.flip (D.pairing.flip a) = D.pairing.flip (D.signs.flip a) :=
  Subtype.ext (z1_k1_commute a.val)

theorem signs_ne_pairing (a : D.points) : D.signs.flip a ≠ D.pairing.flip a :=
  fun h => z1_ne_k1_on_A (D.subset_axes a.property) (congrArg Subtype.val h)

/-- The actual `k1` orbit set, with the induced free sign involution. -/
def signedOrbits : SignedSet D.pairing.Orbit :=
  D.pairing.signedQuotient D.signs D.signs_pairing_commute D.signs_ne_pairing

abbrev Space := D.signedOrbits.Space

/-- The source vector `δ(a)` represented as a signed delta function on `k1` orbits. -/
def vector (a : D.points) : D.Space := D.signedOrbits.delta (D.pairing.orbit a)

@[simp] theorem vector_k (a : D.points) : D.vector (D.pairing.flip a) = D.vector a := by
  simp only [vector, Pairing.orbit_flip]

@[simp] theorem vector_z (a : D.points) : D.vector (D.signs.flip a) = -D.vector a := by
  exact D.signedOrbits.delta_flip (D.pairing.orbit a)

/-- Equality of signed vectors detects the `k1` orbit itself, including its sign. -/
theorem vector_eq_iff (a b : D.points) :
    D.vector a = D.vector b ↔ a = b ∨ a = D.pairing.flip b := by
  change D.signedOrbits.delta _ = D.signedOrbits.delta _ ↔ _
  rw [D.signedOrbits.delta_injective.eq_iff, Pairing.orbit_eq]

instance : Fintype D.pairing.Orbit := Fintype.ofFinite _

/-- The positive definite form with the source's unit signed vectors. -/
def form : LinearMap.BilinForm ℝ D.Space := D.signedOrbits.form

theorem form_pos (v : D.Space) (hv : v ≠ 0) : 0 < D.form v v :=
  D.signedOrbits.form_pos v hv

theorem form_vector_self (a : D.points) : D.form (D.vector a) (D.vector a) = 1 := by
  exact (D.signedOrbits.form_delta _ _).trans (D.signedOrbits.delta_self _)

def basis : Module.Basis D.signedOrbits.toPairing.Orbit ℝ D.Space := D.signedOrbits.basis

theorem basis_orthonormal (a b : D.signedOrbits.toPairing.Orbit) :
    D.form (D.basis a) (D.basis b) = if a = b then 1 else 0 :=
  D.signedOrbits.basis_orthonormal a b

/-- The two independent free involutions divide the dimension by four. -/
theorem four_finrank : Module.finrank ℝ D.Space * 4 = Nat.card D.points := by
  have h₁ := D.signedOrbits.twice_finrank
  change Module.finrank ℝ D.Space * 2 = Nat.card D.pairing.Orbit at h₁
  have h₂ := D.pairing.card_eq_twice (fun a h =>
    k1_fixedPointFree_on_A (D.subset_axes a.property) (congrArg Subtype.val h))
  omega

/-- A genuine permutation action on a stable axis domain induces its signed action. -/
def representation {G : Type*} [Group G] (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a)) :
    Representation ℝ G D.Space :=
  D.pairing.signedRepresentation D.signs D.signs_pairing_commute D.signs_ne_pairing ρ hk hz

theorem representation_kernel_iff {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a)) (g : G) :
    D.representation ρ hk hz g = 1 ↔ ∀ a, ρ g a = a ∨ ρ g a = D.pairing.flip a :=
  D.pairing.signedRepresentation_kernel_iff D.signs D.signs_pairing_commute
    D.signs_ne_pairing ρ hk hz g

theorem representation_vector {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a)) (g : G) (a : D.points) :
    D.representation ρ hk hz g (D.vector a) = D.vector (ρ g a) :=
  D.signedOrbits.representation_delta _ _ g (D.pairing.orbit a)

theorem representation_isometry {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a)) (g : G) (v w : D.Space) :
    D.form (D.representation ρ hk hz g v) (D.representation ρ hk hz g w) = D.form v w :=
  D.signedOrbits.transport_isometry D.signedOrbits (D.pairing.orbitRepresentation ρ hk g)
    (D.pairing.orbitRepresentation_commutes D.signs D.signs_pairing_commute
      D.signs_ne_pairing ρ hk hz g) v w

theorem representation_monomial {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a)) (g : G)
    (a : D.signedOrbits.toPairing.Orbit) :
    ∃ b, D.representation ρ hk hz g (D.basis a) = D.basis b ∨
      D.representation ρ hk hz g (D.basis a) = -D.basis b :=
  D.signedOrbits.representation_monomial _ _ g a

/-- Restrict an ambient permutation action to its invariant axis subset. -/
def restrictPermutations {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hD : ∀ g a, a ∈ D.points ↔ ρ g a ∈ D.points) : G →* Equiv.Perm D.points where
  toFun g := (ρ g).subtypeEquiv (hD g)
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

/-- A concrete ambient action induces the signed spin action. The premises are
only invariance of the domain and commutation with the two actual permutations. -/
def inducedRepresentation {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hD : ∀ g a, a ∈ D.points ↔ ρ g a ∈ D.points)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) : Representation ℝ G D.Space :=
  D.representation (D.restrictPermutations ρ hD)
    (fun g a => Subtype.ext (hk g a.val)) (fun g a => Subtype.ext (hz g a.val))

theorem inducedRepresentation_kernel_iff {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple)
    (hD : ∀ g a, a ∈ D.points ↔ ρ g a ∈ D.points)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G) :
    D.inducedRepresentation ρ hD hk hz g = 1 ↔
      ∀ a ∈ D.points, ρ g a = a ∨ ρ g a = k1.val a := by
  change D.representation _ _ _ g = 1 ↔ _
  rw [D.representation_kernel_iff]
  constructor
  · intro h a ha
    rcases h ⟨a, ha⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · intro h a
    rcases h a.val a.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- Any element inducing the actual `z1` permutation acts as minus identity. -/
theorem representation_of_sign {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm D.points)
    (hk : ∀ g a, ρ g (D.pairing.flip a) = D.pairing.flip (ρ g a))
    (hz : ∀ g a, ρ g (D.signs.flip a) = D.signs.flip (ρ g a))
    (g : G) (hg : ρ g = D.signs.flip) (v : D.Space) :
    D.representation ρ hk hz g v = -v := by
  have he : D.pairing.orbitRepresentation ρ hk g = D.signedOrbits.flip := by
    apply Equiv.ext
    intro a
    induction a using Quotient.inductionOn with
    | h a =>
      change D.pairing.orbit (ρ g a) = D.pairing.orbit (D.signs.flip a)
      rw [hg]
  apply Subtype.ext
  funext a
  change v.val ((D.pairing.orbitRepresentation ρ hk g).symm a) = -v.val a
  rw [he]
  have hh : D.signedOrbits.flip.symm a = D.signedOrbits.flip a := by
    apply D.signedOrbits.flip.injective
    rw [D.signedOrbits.flip.apply_symm_apply, D.signedOrbits.involutive a]
  rw [hh, D.signedOrbits.negative_apply]

/-- In particular `z1` acts as `-1` for every induced spin representation. -/
theorem inducedRepresentation_of_z1 {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple)
    (hD : ∀ g a, a ∈ D.points ↔ ρ g a ∈ D.points)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a))
    (g : G) (hg : ρ g = z1) (v : D.Space) :
    D.inducedRepresentation ρ hD hk hz g v = -v := by
  apply D.representation_of_sign
  apply Equiv.ext
  intro a
  apply Subtype.ext
  exact congrArg (fun e : Equiv.Perm Triple => e a.val) hg

end SpinDomain

abbrev B1A2 := secondAxisDomain.Space
abbrev B1A3 := thirdAxisDomain.Space
abbrev SpinSpace := bothAxesDomain.Space
abbrev SpinDirectSum := B1A2 × B1A3

theorem finrank_B1A2 : Module.finrank ℝ B1A2 = 2048 := by
  have h := secondAxisDomain.four_finrank
  change Module.finrank ℝ B1A2 * 4 = Nat.card A2 at h
  rw [axis2_card] at h
  omega

theorem finrank_B1A3 : Module.finrank ℝ B1A3 = 2048 := by
  have h := thirdAxisDomain.four_finrank
  change Module.finrank ℝ B1A3 * 4 = Nat.card A3 at h
  rw [axis3_card] at h
  omega

theorem finrank_spinSpace : Module.finrank ℝ SpinSpace = 4096 := by
  have h := bothAxesDomain.four_finrank
  change Module.finrank ℝ SpinSpace * 4 = Nat.card A at h
  rw [spinAxes_card] at h
  omega

theorem finrank_spinDirectSum : Module.finrank ℝ SpinDirectSum = 4096 := by
  rw [Module.finrank_prod, finrank_B1A2, finrank_B1A3]

def delta2 (b : ParkerLoop) : B1A2 := secondAxisDomain.vector (axis2Equiv b)
def delta3 (b : ParkerLoop) : B1A3 := thirdAxisDomain.vector (axis3Equiv b)

@[simp] theorem delta2_sign (b : ParkerLoop) : delta2 (parkerSign 1 b) = -delta2 b := by
  have h : axis2Equiv (parkerSign 1 b) = secondAxisDomain.signs.flip (axis2Equiv b) :=
    Subtype.ext (z1_axis2 b).symm
  exact (congrArg secondAxisDomain.vector h).trans (secondAxisDomain.vector_z _)

@[simp] theorem delta3_sign (b : ParkerLoop) : delta3 (parkerSign 1 b) = -delta3 b := by
  have h : axis3Equiv (parkerSign 1 b) = thirdAxisDomain.signs.flip (axis3Equiv b) :=
    Subtype.ext (z1_axis3 b).symm
  exact (congrArg thirdAxisDomain.vector h).trans (thirdAxisDomain.vector_z _)

@[simp] theorem delta2_omega (b : ParkerLoop) :
    delta2 (parkerLoopMultiply b parkerOmega) = delta2 b := by
  have h : axis2Equiv (parkerLoopMultiply b parkerOmega) =
      secondAxisDomain.pairing.flip (axis2Equiv b) := Subtype.ext (k1_axis2 b).symm
  exact (congrArg secondAxisDomain.vector h).trans (secondAxisDomain.vector_k _)

@[simp] theorem delta3_signOmega (b : ParkerLoop) :
    delta3 (parkerLoopMultiply b (parkerSign 1 parkerOmega)) = delta3 b := by
  have h : axis3Equiv (parkerLoopMultiply b (parkerSign 1 parkerOmega)) =
      thirdAxisDomain.pairing.flip (axis3Equiv b) := Subtype.ext (k1_axis3 b).symm
  exact (congrArg thirdAxisDomain.vector h).trans (thirdAxisDomain.vector_k _)

theorem delta2_norm (b : ParkerLoop) : secondAxisDomain.form (delta2 b) (delta2 b) = 1 :=
  secondAxisDomain.form_vector_self _

theorem delta3_norm (b : ParkerLoop) : thirdAxisDomain.form (delta3 b) (delta3 b) = 1 :=
  thirdAxisDomain.form_vector_self _

/-- The special generator fixes the second axis and follows `k1` on the third. -/
theorem psi2_signOmega_orbits {a : Triple} (ha : a ∈ A) :
    psi2 (parkerSign 1 parkerOmega) a = a ∨
      psi2 (parkerSign 1 parkerOmega) a = k1.val a := by
  rcases ha with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · left
    simp only [axis2, psi2_apply, loopInverse_signOmega, signOmega_sandwich,
      rightZero_none, leftZero_none]
  · right
    rw [k1_axis3]
    simp only [axis3, psi2_apply, loopInverse_signOmega, leftZero_none,
      rightZero_none, signOmega_commutes_zero, rightZero_some]

/-- Source 27.5(4), on the spin factor, for every action with this ambient element. -/
theorem spin_inducedRepresentation_of_psi2_signOmega {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A ↔ ρ g a ∈ A)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a))
    (g : G) (hg : ρ g = psi2 (parkerSign 1 parkerOmega)) :
    bothAxesDomain.inducedRepresentation ρ hA hk hz g = 1 := by
  apply (bothAxesDomain.inducedRepresentation_kernel_iff ρ hA hk hz g).2
  intro a ha
  rw [hg]
  exact psi2_signOmega_orbits ha

end Sporadic.Monster.Construction.TrialitySpin
