module

public import Theory.SpecificGroups.LieType.FiniteParabolicRealization
public import Theory.GroupTheory.InvariantLeviDecomposition

/-!
# Descent of invariant Levi decompositions

For a sigma-stable algebraic decomposition `P = U L` with disjoint factors,
uniqueness makes the factors of each fixed element fixed. Fixed unipotent
points already lie in `O^{p'}(K^sigma)`. Thus this decomposition restricts to
the source finite group, including its actual Levi complement. The relative
quotient constructs a surjective projection, with kernel the restricted
unipotent subgroup inside the restricted parabolic.

The algebraic geometry, rational conjugacy of invariant parabolics, trivial
p-core of the finite Levi, and existence of nonidentity fixed radical points
remain explicit source obligations. This module's conditional descent
results do not assert those geometric theorems.

Source: GLS3, Theorems 1.13.3(a,b), 2.6.5(e,g) and Proposition 2.6.8.
-/

namespace Theory.AlgebraicGroup.InvariantParabolicLevi

open FiniteParabolicRealization

variable {k : Type*} [Field k] [IsAlgClosed k] {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- An invariant algebraic factorization descends to the source residual.
The unipotent factor lies in that residual, so the other factor does too. -/
public theorem restrict_factorization (P U L : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l) :
    ∀ x ∈ restrict σ p P.toSubgroup,
      ∃ u ∈ restrict σ p U.toSubgroup,
        ∃ l ∈ restrict σ p L.toSubgroup, x = u * l := by
  intro x hx
  obtain ⟨u, hu, l, hl, heq⟩ := hmul (pointEmbedding σ p x) hx
  have hfix : σ.onPoints (u * l) = u * l := by
    rw [← heq]
    exact x.val.property
  obtain ⟨huFix, _⟩ := Subgroup.fixed_factors_of_disjoint
    σ.onPoints U.toSubgroup L.toSubgroup hdis hσU hσL hu hl hfix
  let u' : definingGroup σ p :=
    ⟨⟨u, huFix⟩, fixed_unipotent_le_definingGroup σ p U hU hu⟩
  refine ⟨u', hu, u'⁻¹ * x, ?_, by simp⟩
  change pointEmbedding σ p (u'⁻¹ * x) ∈ L.toSubgroup
  rw [map_mul, map_inv, heq]
  change u⁻¹ * (u * l) ∈ L.toSubgroup
  simpa only [inv_mul_cancel_left] using (show l ∈ L.toSubgroup from hl)

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
/-- Restriction preserves disjointness because the point embedding is injective. -/
public theorem restrict_disjoint (U L : Subgroup (Variety.Point K))
    (hdis : Disjoint U L) : Disjoint (restrict σ p U) (restrict σ p L) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  change x = 1
  apply pointEmbedding_injective σ p
  rw [map_one]
  exact disjoint_iff_inf_le.mp hdis hx

/-- Construct the finite Levi projection from the algebraic decomposition.
Its target is the restricted algebraic Levi itself, and its kernel is relative
to the restricted parabolic. In particular no quotient realization or finite
projection is assumed. -/
public theorem exists_finiteLeviProjection (P U L : ClosedSubgroup K)
    (hLP : L.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l) :
    ∃ f : restrict σ p P.toSubgroup →* restrict σ p L.toSubgroup,
      Function.Surjective f ∧
      f.ker = (restrict σ p U.toSubgroup).subgroupOf (restrict σ p P.toSubgroup) ∧
      ∀ l : restrict σ p L.toSubgroup,
        f ⟨l, restrict_mono σ p hLP l.property⟩ = l := by
  exact Subgroup.exists_projection_of_disjoint_factorization
    (restrict σ p P.toSubgroup) (restrict σ p U.toSubgroup)
    (restrict σ p L.toSubgroup) (restrict_mono σ p hLP)
    (restrict_normal σ p _ _ hN) (restrict_disjoint σ p _ _ hdis)
    (restrict_factorization σ p P U L hU hdis hσU hσL hmul)

/-- Application to GLS3 2.6.5(e): the constructed projection discharges the
finite projection and kernel premises of the parent's transfer theorem.
The geometric decomposition and the finite Levi's trivial p-core remain
explicit and must be proved for the source standard parabolics. -/
public theorem radical_eq_pCore_of_decomposition
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (P U L : ClosedSubgroup K)
    (hUP : U.toSubgroup ≤ P.toSubgroup) (hLP : L.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l)
    (hLcore : pCore p (restrict σ p L.toSubgroup) = ⊥) :
    restrict σ p U.toSubgroup =
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype := by
  obtain ⟨f, hf, hker, -⟩ :=
    exists_finiteLeviProjection σ p P U L hLP hN hU hdis hσU hσL hmul
  exact restrict_eq_embedded_pCore_of_leviProjection σ p P U hUP hU f hf hker hLcore

end Theory.AlgebraicGroup.InvariantParabolicLevi
