module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.CentralField

/-!
# The forced central field on arbitrary triple-Mathieu modules

The central element supplies F₄ scalars on the original binary vector space.
Every binary invariant subspace is stable under these scalars, since each
scalar is a binary linear combination of the identity and the central element.
Thus the full invariant-subspace lattices agree, and the same faithful action
is irreducible over F₄. Its binary dimension is twice its F₄ dimension.

This reduction retains the actual cover and central scalar. It does not
assume absolute irreducibility or identify the full endomorphism field.
Source: Aschbacher–Smith H.12.1, printed pp.393–394; Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
open Representation Uniqueness.PointRestriction

/-- A single missing degree branch for actual F₄ actions of the triple cover.
The central element must act by the distinguished primitive scalar. This is a
mathematical exclusion to be proved; it is not a classification axiom. -/
def CentralFieldDegreeExclusion (d : ℕ) : Prop :=
  ∀ (W : Type*) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (τ : Representation F M22TripleCover W),
    Function.Injective τ → τ.IsIrreducible →
    (∀ w, τ scalar w = (QuadraticAlgebra.omega : F) • w) →
    Module.finrank F W = d → False

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ)

/-- The full group has the same invariant subspaces over the forced central field. -/
def subrepresentationEquiv : letI := fieldModule ρ hf
    Subrepresentation ρ ≃o Subrepresentation (fieldRepresentation ρ hf) := by
  letI := fieldModule ρ hf
  letI := fieldTower ρ hf
  refine {
    toFun := fun U => {
      toSubmodule := {
        carrier := U
        zero_mem' := U.toSubmodule.zero_mem
        add_mem' := U.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    invFun := fun U => {
      toSubmodule := U.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro r v hv
    change r.re • v + r.im • ρ scalar v ∈ U.toSubmodule
    exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hv)
      (U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule scalar hv))
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl

/-- Binary irreducibility implies irreducibility over the canonical F₄ scalars. -/
theorem fieldRepresentation_isIrreducible : letI := fieldModule ρ hf
    IsIrreducible (fieldRepresentation ρ hf) := by
  let := fieldModule ρ hf
  exact (subrepresentationEquiv ρ hf).isSimpleOrder_iff.mp inferInstance

/-- The dimension formula holds for arbitrary degrees, not just degree twelve. -/
theorem twice_field_finrank : letI := fieldModule ρ hf
    2 * Module.finrank F V = Module.finrank (ZMod 2) V := by
  let := fieldModule ρ hf
  let := fieldTower ρ hf
  have h := Module.finrank_mul_finrank (ZMod 2) F V
  rwa [QuadraticAlgebra.finrank_eq_two] at h

/-- The original finite-dimensional binary space remains finite-dimensional
 over its canonically constructed central field. -/
theorem field_finiteDimensional [FiniteDimensional (ZMod 2) V] :
    letI := fieldModule ρ hf
    FiniteDimensional F V := by
  let := fieldModule ρ hf
  let := fieldTower ρ hf
  exact Module.Finite.of_restrictScalars_finite (ZMod 2) F V

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
