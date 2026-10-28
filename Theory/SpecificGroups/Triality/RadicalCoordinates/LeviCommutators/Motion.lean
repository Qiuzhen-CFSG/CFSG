module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.Actors
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic

/-!
# From a nontrivial torus weight to radical commutator membership

For an additive root parametrization x, an actor with
h x(t) h⁻¹ = x(c t), c ≠ 1, puts every root element in the subgroup
commutator: use [h,x(t/(c-1))]. No normalization premise is needed.
The triality adapters retain the actual split Geck equations and descend
them through the elementary group to the genuine carrier.

The motion predicates below are explicit matrix-action inputs, not claims
that the required nontrivial weights have been constructed. Their arithmetic
and concrete torus-action proofs are separate from this implication.

Source: the torus relations of GLS3 §2.4, used in the local perfectness
argument of Aschbacher–Smith F.1.12(II), printed pp.263–264.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics ConcreteBruhat
open scoped commutatorElement

/-- A nontrivial scalar action of an actual folded Levi torus word on a short root. -/
def ShortTorusMotion (P : Parameters) (hp : P.prime = 2) (a : Node) (i : Fin 3) : Prop :=
  ∃ t : (RootField P a)ˣ, ∃ c : ExtensionField P, c ≠ 1 ∧ ∀ u,
    elementaryInclusion P (torusElementary P hp a t) * shortSplit P i u *
      (elementaryInclusion P (torusElementary P hp a t))⁻¹ = shortSplit P i (c * u)

/-- A nontrivial scalar action on a long root, with scalar in the actual fixed field. -/
def LongTorusMotion (P : Parameters) (hp : P.prime = 2) (a : Node) (i : Fin 3) : Prop :=
  ∃ t : (RootField P a)ˣ, ∃ c : fixedField P, c ≠ 1 ∧ ∀ u,
    elementaryInclusion P (torusElementary P hp a t) * longSplit P i u *
      (elementaryInclusion P (torusElementary P hp a t))⁻¹ = longSplit P i (c * u)

private theorem mem_commutator_of_scaling {F G : Type*} [Field F] [Group G]
    (U L : Subgroup G) (x : F → G) (hx0 : x 0 = 1)
    (hxadd : ∀ s t, x (s + t) = x s * x t) (hU : ∀ t, x t ∈ U)
    (h : G) (hL : h ∈ L) (c : F) (hc : c ≠ 1)
    (haction : ∀ t, h * x t * h⁻¹ = x (c * t)) (t : F) : x t ∈ ⁅U, L⁆ := by
  have hxinv (u : F) : (x u)⁻¹ = x (-u) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← hxadd, add_neg_cancel, hx0]
  have he (u : F) : ⁅h, x u⁆ = x ((c - 1) * u) := by
    rw [commutatorElement_def, haction, hxinv, ← hxadd]
    congr 1
    ring
  have hm := Subgroup.commutator_mem_commutator hL (hU (t / (c - 1)))
  rw [Subgroup.commutator_comm L U, he] at hm
  have hscalar : (c - 1) * (t / (c - 1)) = t := by
    field_simp [sub_ne_zero.mpr hc]
  rwa [hscalar] at hm

/-- A split short-root action equation implies membership after actual descent. -/
theorem short_mem_commutator_of_motion (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i : Fin 3) (hi : shortSupported a i)
    (hm : ShortTorusMotion P hp a i) (u : ExtensionField P) :
    short P hp i u ∈ ⁅descendSubgroup P (rootSubgroup P a), levi P a⁆ := by
  obtain ⟨t, c, hc, hact⟩ := hm
  apply mem_commutator_of_scaling _ _ (short P hp i) (short_zero P hp i)
    (short_add P hp i) (short_mem P hp a i hi) (torusActor P hp a t)
    (torusActor_mem_levi P hp a t) c hc
  intro v
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val]
  exact hact v

/-- The analogous descent for a fixed-field singleton root. -/
theorem long_mem_commutator_of_motion (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i : Fin 3) (hi : longSupported a i)
    (hm : LongTorusMotion P hp a i) (u : fixedField P) :
    long P hp i u ∈ ⁅descendSubgroup P (rootSubgroup P a), levi P a⁆ := by
  obtain ⟨t, c, hc, hact⟩ := hm
  apply mem_commutator_of_scaling _ _ (long P hp i) (long_zero P hp i)
    (long_add P hp i) (long_mem P hp a i hi) (torusActor P hp a t)
    (torusActor_mem_levi P hp a t) c hc
  intro v
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, longElementary_val]
  exact hact v

end Triality.Standard.RadicalCoordinates.LeviCommutators
