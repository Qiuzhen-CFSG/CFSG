module

public import Theory.SpecificGroups.LieType.FiniteReductivePCore
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.Tori.DefiningCharacteristic

/-!
# The closed algebraic Levi and its literal finite intersection

Restrict the ambient endomorphism to a stable closed subgroup by algebraic
codomain restriction. Exact invariance gives surjectivity, and inclusion
identifies its fixed group with the intersection inside the ambient fixed
group. Thus ambient finiteness also proves that the restriction is Steinberg.
This constructs the comparison, rather than assuming a model isomorphism.

On this actual closed Levi, a positive Sylow in its own defining group and a
fixed opposition element with disjoint unipotent factors imply trivial p-core
of the full fixed group and then of the intersection with the *ambient*
defining group. The final theorem supplies this conclusion to the constructed
finite Levi projection. Its normality and kernel conventions are unchanged.

For a reductive Levi, the positive Sylow and opposition geometry must still
be produced by the finite Bruhat theory. These remain explicit parameters:
this file does not assert their existence from reductivity. The algebraic
Levi decomposition comes from the standard-parabolic geometry. No small
field or twisted case is excluded. The opposition convention is left
conjugation `n * x * n⁻¹`; invert a source right-conjugation representative.

The toral Levi branch is proved directly from the absence of defining-
characteristic torsion in a torus, without the Sylow or opposition premises.

Sources: GLS3, 2.1.10, 2.3.4--2.3.8, 2.6.2 and 2.6.5(e,f,g).
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteReductivePCore
open FiniteParabolicRealization
variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- The actual restriction of sigma to an invariant closed Levi. -/
def leviEndomorphism (σ : AlgebraicEndomorphism K) (L : ClosedSubgroup K)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L) : AlgebraicEndomorphism L.carrierVariety :=
  (σ.comp L.inclusion).codRestrictClosedSubgroup L
    (fun x => hσL _ (L.pointEquiv x).property)

theorem leviEndomorphism_inclusion (σ : AlgebraicEndomorphism K) (L : ClosedSubgroup K)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L) (x : Variety.Point L.carrierVariety) :
    L.inclusion.onPoints ((leviEndomorphism σ L hσL).onPoints x) =
      σ.onPoints (L.inclusion.onPoints x) :=
  Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ x

/-- The fixed group in the closed Levi is the literal intersection with the
ambient fixed group. -/
def closedFixedPointsEquiv (σ : AlgebraicEndomorphism K) (L : ClosedSubgroup K)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L) :
    fixedPoints (leviEndomorphism σ L hσL) ≃* fullFixed σ L.toSubgroup where
  toFun x := ⟨⟨L.inclusion.onPoints x, by
      change σ.onPoints (L.inclusion.onPoints x) = L.inclusion.onPoints x
      rw [← leviEndomorphism_inclusion σ L hσL]
      exact congrArg L.inclusion.onPoints x.property⟩, (L.pointEquiv x).property⟩
  invFun x := ⟨L.pointEquiv.symm ⟨x.val.val, x.property⟩, by
      apply L.inclusion_injective
      rw [leviEndomorphism_inclusion]
      change σ.onPoints x.val.val = x.val.val
      exact x.val.property⟩
  left_inv x := by
    apply Subtype.ext
    exact L.pointEquiv.symm_apply_apply x.val
  right_inv x := rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact L.inclusion.onPoints.map_mul x.val y.val

theorem closedFixedPointsEquiv_inclusion (σ : AlgebraicEndomorphism K)
    (L : ClosedSubgroup K) (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (x : fixedPoints (leviEndomorphism σ L hσL)) :
    fullFixedPointEmbedding σ L.toSubgroup (closedFixedPointsEquiv σ L hσL x) =
      L.inclusion.onPoints x := rfl

/-- Exact sigma-invariance makes the restricted endomorphism surjective;
its fixed points inject into the finite ambient fixed group. -/
theorem leviEndomorphism_isSteinberg (σ : AlgebraicEndomorphism K)
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (L : ClosedSubgroup K) (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (himage : L.toSubgroup.map σ.onPoints = L.toSubgroup) :
    IsAlgebraicSteinbergEndomorphism (leviEndomorphism σ L hσL) := by
  refine ⟨?_, ?_⟩
  · intro y
    have hy : L.inclusion.onPoints y ∈ L.toSubgroup.map σ.onPoints := by
      rw [himage]
      exact (L.pointEquiv y).property
    obtain ⟨x, hx, heq⟩ := hy
    refine ⟨L.pointEquiv.symm ⟨x, hx⟩, ?_⟩
    apply L.inclusion_injective
    rw [leviEndomorphism_inclusion]
    exact heq
  · exact Finite.of_injective (closedFixedPointsEquiv σ L hσL)
      (closedFixedPointsEquiv σ L hσL).injective

/-- Transfer from the intrinsic closed fixed group to the actual ambient
residual intersection. No equality of the two residuals is assumed. -/
theorem restrict_pCore_eq_bot_iff_closedFixed (σ : AlgebraicEndomorphism K) (p : ℕ)
    (L : ClosedSubgroup K) (hσL : ∀ l ∈ L, σ.onPoints l ∈ L) :
    pCore p (restrict σ p L.toSubgroup) = ⊥ ↔
      pCore p (fixedPoints (leviEndomorphism σ L hσL)) = ⊥ := by
  rw [restrict_pCore_eq_bot_iff]
  let e := closedFixedPointsEquiv σ L hσL
  constructor
  · intro h
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso, h, Subgroup.map_bot]
  · intro h
    rw [← pCore_map_iso p e, h, Subgroup.map_bot]

/-- Positive Sylow and opposition inputs on the algebraic Levi itself imply
p-reducedness of its intersection with the ambient defining group. -/
theorem restrict_pCore_eq_bot_of_closedLevi_opposition
    (σ : AlgebraicEndomorphism K) (p : ℕ)
    (L : ClosedSubgroup K) (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (V : ClosedSubgroup L.carrierVariety)
    (S : Sylow p (definingGroup (leviEndomorphism σ L hσL) p))
    (hS : (S : Subgroup _) = restrict (leviEndomorphism σ L hσL) p V.toSubgroup)
    (n : fixedPoints (leviEndomorphism σ L hσL))
    (hopp : Disjoint V.toSubgroup
      (V.toSubgroup.map (MulAut.conj (n : Variety.Point L.carrierVariety)).toMonoidHom)) :
    pCore p (restrict σ p L.toSubgroup) = ⊥ := by
  apply (restrict_pCore_eq_bot_iff_closedFixed σ p L hσL).mpr
  apply Subgroup.pCore_eq_bot_of_residualSylow_opposition p
    (fixedPoints (leviEndomorphism σ L hσL)).subtype Subtype.coe_injective
    V.toSubgroup S ?_ n hopp
  rintro x ⟨s, hs, rfl⟩
  rw [hS] at hs
  exact hs

/-- The toral Levi branch needs no finite Bruhat input: tori have no
nonidentity p-power torsion in characteristic p. -/
theorem restrict_pCore_eq_bot_of_isSubtorus (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact p.Prime] [CharP k p] (L : ClosedSubgroup K) (hL : IsSubtorus L) :
    pCore p (restrict σ p L.toSubgroup) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨a, ha⟩ := pCore_isPGroup (p := p) (G := restrict σ p L.toSubgroup) ⟨x, hx⟩
  have hpow : x ^ (p ^ a) = 1 :=
    congrArg (pCore p (restrict σ p L.toSubgroup)).subtype ha
  have hpoint : pointEmbedding σ p x ^ (p ^ a) = 1 := by
    simpa only [map_pow, map_one, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg ((pointEmbedding σ p).comp (restrict σ p L.toSubgroup).subtype) hpow
  change x = 1
  apply Subtype.ext
  apply pointEmbedding_injective σ p
  rw [Subgroup.coe_one, map_one]
  exact hL.eq_one_of_mem_of_pow_prime_pow_eq_one x.property a hpoint

section Application
variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact p.Prime] [CharP k p] [Fact (IsAlgebraicSteinbergEndomorphism σ)]

/-- This supplies exactly the hLcore argument to the finite Levi projection
consumer. The positive Sylow and fixed opposition element still come from
the earlier finite Bruhat/root geometry for the reductive closed Levi. -/
theorem radical_eq_pCore_of_closedLevi_opposition
    (P U L : ClosedSubgroup K)
    (hUP : U.toSubgroup ≤ P.toSubgroup) (hLP : L.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l)
    (V : ClosedSubgroup L.carrierVariety)
    (S : Sylow p (definingGroup (leviEndomorphism σ L hσL) p))
    (hS : (S : Subgroup _) = restrict (leviEndomorphism σ L hσL) p V.toSubgroup)
    (n : fixedPoints (leviEndomorphism σ L hσL))
    (hopp : Disjoint V.toSubgroup
      (V.toSubgroup.map (MulAut.conj (n : Variety.Point L.carrierVariety)).toMonoidHom)) :
    restrict σ p U.toSubgroup =
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype :=
  InvariantParabolicLevi.radical_eq_pCore_of_decomposition σ p P U L
    hUP hLP hN hU hdis hσU hσL hmul
    (restrict_pCore_eq_bot_of_closedLevi_opposition σ p L hσL V S hS n hopp)
/-- The radical equals the finite p-core when the algebraic Levi is a torus.
This discharges the toral branch directly, including the Borel case. -/
theorem radical_eq_pCore_of_toralLevi
    (P U L : ClosedSubgroup K)
    (hUP : U.toSubgroup ≤ P.toSubgroup) (hLP : L.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l)
    (hL : IsSubtorus L) :
    restrict σ p U.toSubgroup =
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype :=
  InvariantParabolicLevi.radical_eq_pCore_of_decomposition σ p P U L
    hUP hLP hN hU hdis hσU hσL hmul
    (restrict_pCore_eq_bot_of_isSubtorus σ p L hL)

end Application

end Theory.AlgebraicGroup.FiniteReductivePCore
