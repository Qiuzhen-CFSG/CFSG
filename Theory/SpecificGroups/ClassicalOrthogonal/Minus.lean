module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.QuadraticSpace
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.ProjectiveOmega
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.IsPrimePow

/-!
# Finite projective orthogonal groups of minus type

For a finite field `F` and `r ≥ 2`, the natural quadratic space is the
orthogonal sum of `r - 1` hyperbolic planes and an anisotropic plane. Its
form is constructed over every finite field, including characteristic two;
`quadraticForm_minus_type` certifies dimension `2r`, nonsingularity, and
Witt index `r - 1`.

`ClassicalGroup.POmegaMinus r F` is the commutator subgroup of the full
quadratic isometry group, modulo the scalar transformations it contains.
The imported kernel theorem proves that projectivization removes exactly
those transformations. Both the group structure and finiteness come from
this independent construction. The isomorphism predicate is suitable for
catalogue consumers and is invariant under multiplicative equivalence.

The family includes rank two over every finite field, including `F₂`:
there is no exclusion at `(r,q) = (2,2)`. This is the usual rank-two minus
family, also denoted `PSL₂(q²)`. No exceptional isomorphism is needed for
its inclusion, since its four-dimensional orthogonal carrier is constructed
directly. `IsPOmegaMinus.exists_model` supplies a model for every prime
power and every rank, in particular every rank at least two.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 3,
Theorem 2.2.7 and §2.7 (`refs/KGroup/GLS3/chapter2.tex`). No simplicity
or classification assumption enters the construction.
-/

@[expose] public section

universe u v

namespace ClassicalOrthogonal.Minus

variable (F : Type u) [Field F] [Finite F]

/-- The chosen minus quadratic form in rank `r`. -/
noncomputable def quadraticForm (r : ℕ) : QuadraticForm F (Space F (r - 1)) :=
  form F (r - 1) (parameter F)

/-- The anisotropic plane used by the model actually exists over its field. -/
theorem quadraticForm_anisotropic_plane : (plane F (parameter F)).Anisotropic :=
  plane_anisotropic F (parameter F) (parameter_spec F)

/-- Nonsingularity is stated for the polar form without dividing by two. -/
theorem quadraticForm_nonsingular (r : ℕ) : (quadraticForm F r).polarBilin.Nondegenerate :=
  form_nonsingular F (r - 1) (parameter F) (parameter_spec F)

/-- The dimension and exact Witt-index certificate for the minus family.
The final conjunct bounds every totally singular subspace, not only ones
containing the displayed coordinate subspace. -/
theorem quadraticForm_minus_type (r : ℕ) (hr : 2 ≤ r) :
    Module.finrank F (Space F (r - 1)) = 2 * r ∧
    (quadraticForm F r).polarBilin.Nondegenerate ∧
    (∃ U : Submodule F (Space F (r - 1)),
      Module.finrank F U = r - 1 ∧ (∀ v ∈ U, quadraticForm F r v = 0)) ∧
    (∀ W : Submodule F (Space F (r - 1)),
      (∀ v ∈ W, quadraticForm F r v = 0) → Module.finrank F W ≤ r - 1) := by
  refine ⟨?_, quadraticForm_nonsingular F r, ?_, ?_⟩
  · rw [space_finrank]
    omega
  · exact ⟨singularSubspace F (r - 1), singularSubspace_finrank F (r - 1),
      form_eq_zero_on_singularSubspace F (r - 1) (parameter F)⟩
  · exact singular_finrank_le F (r - 1) (parameter F) (parameter_spec F)

end ClassicalOrthogonal.Minus

namespace ClassicalGroup

/-- The actual finite minus-type projective orthogonal group. Rank two is
retained, including over the field of two elements. -/
abbrev POmegaMinus (r : ℕ) (F : Type u) [Field F] [Finite F] :=
  ClassicalOrthogonal.Minus.ProjectiveOmega F (ClassicalOrthogonal.Minus.Space F (r - 1))
    (ClassicalOrthogonal.Minus.quadraticForm F r)

/-- Finiteness follows from the finite natural quadratic space. -/
instance pOmegaMinus_finite (r : ℕ) (F : Type u) [Field F] [Finite F] :
    Finite (POmegaMinus r F) := inferInstance

/-- Isomorphism to the constructed `PΩ⁻_{2r}(q)` over a field of order `q`. -/
def IsPOmegaMinus (G : Type u) [Group G] (r q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* POmegaMinus r F)

/-- The carrier witnesses its own isomorphism predicate. -/
theorem IsPOmegaMinus.self (r : ℕ) (F : Type) [Field F] [Finite F] :
    IsPOmegaMinus (POmegaMinus r F) r (Nat.card F) :=
  ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩

variable {G : Type u} {H : Type v} [Group G] [Group H] {r q : ℕ}

/-- Transport a minus orthogonal model across a group isomorphism. -/
theorem IsPOmegaMinus.of_mulEquiv (h : IsPOmegaMinus G r q) (e : H ≃* G) :
    IsPOmegaMinus H r q := by
  rcases h with ⟨F, hF, hfin, hq, ⟨f⟩⟩
  exact ⟨F, hF, hfin, hq, ⟨e.trans f⟩⟩

/-- Finiteness is a consequence of having a model. -/
theorem IsPOmegaMinus.finite (h : IsPOmegaMinus G r q) : Finite G := by
  rcases h with ⟨F, hF, hfin, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

/-- The model predicate is invariant under multiplicative equivalence. -/
theorem isPOmegaMinus_mulEquiv_iff (e : G ≃* H) :
    IsPOmegaMinus G r q ↔ IsPOmegaMinus H r q :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- Every prime power supplies an actual finite model. This includes rank
two and `q = 2`; no anisotropic-form witness is left for the caller to provide. -/
theorem IsPOmegaMinus.exists_model (r q : ℕ) (hq : IsPrimePow q) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsPOmegaMinus G r q := by
  obtain ⟨p, e, hp, he, hq⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p e
  refine ⟨POmegaMinus r F, inferInstance, inferInstance, F, inferInstance, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  exact (GaloisField.card p e (Nat.ne_of_gt he)).trans hq

end ClassicalGroup
