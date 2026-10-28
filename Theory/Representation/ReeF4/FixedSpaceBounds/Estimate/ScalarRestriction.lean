module

public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Fixed codimension on restriction of scalars

A nonzero invariant subspace over a smaller coefficient field spans the whole
of an irreducible representation over the larger field. Consequently its
restricted action is faithful whenever the original action is faithful. A
minimal such subspace supplies a faithful irreducible representation over the
smaller field. Its subgroup-fixed codimension is bounded by the original
codimension multiplied by the field degree.

This is the finite-field descent needed in Guralnick--Malle, *Classification
of 2F-modules, II*, Lemma 8.8. Restriction of scalars itself need not be
irreducible. No semisimplicity or absolute irreducibility is assumed.
-/

public section
open Representation
namespace ReeF4.FixedSpaceEstimate
variable {F E G W : Type*} [Field F] [Field E] [Algebra F E]
  [Group G] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
  [FiniteDimensional F E] [FiniteDimensional E W]

omit [FiniteDimensional F E] [FiniteDimensional E W] in
/-- Every nonzero subrepresentation over the smaller field spans the original module. -/
theorem scalarSpan_eq_top (σ : Representation E G W) [σ.IsIrreducible]
    (U : Subrepresentation (restrictScalars (k := F) σ)) (hU : U ≠ ⊥) :
    Submodule.span E (U : Set W) = ⊤ := by
  let S : Subrepresentation σ := {
    toSubmodule := Submodule.span E (U : Set W)
    apply_mem_toSubmodule g := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => exact Submodule.subset_span (U.apply_mem_toSubmodule g hw)
      | zero => simp
      | add x y _ _ hx hy => simpa using (Submodule.span E (U : Set W)).add_mem hx hy
      | smul a x _ hx => simpa using (Submodule.span E (U : Set W)).smul_mem a hx }
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    apply hU
    apply bot_unique
    intro w hw
    have : w ∈ S := Submodule.subset_span hw
    rw [hS] at this
    exact (show w = 0 from this)
  · exact congrArg Subrepresentation.toSubmodule hS

/-- Scalar restriction contains a faithful irreducible subrepresentation. -/
theorem exists_faithful_scalar_subrepresentation
    (σ : Representation E G W) [σ.IsIrreducible] (hf : Function.Injective σ) :
    ∃ U : Subrepresentation (restrictScalars (k := F) σ),
      U.toRepresentation.IsIrreducible ∧ Function.Injective U.toRepresentation := by
  let : FiniteDimensional F W := Module.Finite.trans (R := F) E W
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨U, hU, _⟩ :=
    (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (restrictScalars (k := F) σ))).resolve_left
      top_ne_bot
  refine ⟨U, (Subrepresentation.irreducible_iff_isAtom U).mpr hU, ?_⟩
  intro g h hgh
  apply hf
  ext w
  have hw : w ∈ Submodule.span E (U : Set W) := by
    rw [scalarSpan_eq_top σ U hU.ne_bot]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw => exact congrArg (fun f : Module.End F U.toSubmodule => (f ⟨w, hw⟩).val) hgh
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

/-- Passing to an invariant subspace cannot increase fixed-space codimension. -/
theorem subrepresentation_fixedCodim_le
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V)
    (U : Subrepresentation ρ) (A : Subgroup G) :
    Module.finrank k (U.toSubmodule ⧸ invariants (U.toRepresentation.comp A.subtype)) ≤
      Module.finrank k (V ⧸ invariants (ρ.comp A.subtype)) := by
  let C := invariants (ρ.comp A.subtype)
  let D := invariants (U.toRepresentation.comp A.subtype)
  let e : D ≃ₗ[k] (U.toSubmodule ⊓ C : Submodule k V) := {
    toFun := fun w => ⟨w.val, w.val.property, fun a => congrArg Subtype.val (w.property a)⟩
    invFun := fun w => ⟨⟨w, w.property.1⟩, fun a => Subtype.ext (w.property.2 a)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have he := e.finrank_eq
  have hU := D.finrank_quotient_add_finrank
  have hV := C.finrank_quotient_add_finrank
  have hs := U.toSubmodule.finrank_sup_add_finrank_inf_eq C
  have ht := (U.toSubmodule ⊔ C).finrank_le
  change Module.finrank k (U.toSubmodule ⧸ D) ≤ Module.finrank k (V ⧸ C)
  omega

omit [FiniteDimensional F E] [FiniteDimensional E W] in
/-- The literal fixed-space quotient obeys the scalar dimension tower. -/
theorem fixedCodim_restrictScalars
    (σ : Representation E G W) (A : Subgroup G) :
    Module.finrank F (W ⧸ invariants ((restrictScalars (k := F) σ).comp A.subtype)) =
      Module.finrank F E * Module.finrank E (W ⧸ invariants (σ.comp A.subtype)) := by
  have he : invariants ((restrictScalars (k := F) σ).comp A.subtype) =
      (invariants (σ.comp A.subtype)).restrictScalars F := rfl
  rw [he, (Submodule.Quotient.restrictScalarsEquiv F
    (invariants (σ.comp A.subtype))).finrank_eq, Module.finrank_mul_finrank]

/-- A bound on faithful irreducibles over the smaller field applies to the original action. -/
theorem fixedCodim_ge_of_scalar_irreducibles
    (σ : Representation E G W) [σ.IsIrreducible] (hf : Function.Injective σ)
    (A : Subgroup G) (b : ℕ)
    (hbound : ∀ U : Subrepresentation (restrictScalars (k := F) σ),
      U.toRepresentation.IsIrreducible → Function.Injective U.toRepresentation →
        b ≤ Module.finrank F (U.toSubmodule ⧸ invariants (U.toRepresentation.comp A.subtype))) :
    b ≤ Module.finrank F E * Module.finrank E (W ⧸ invariants (σ.comp A.subtype)) := by
  let : FiniteDimensional F W := Module.Finite.trans (R := F) E W
  obtain ⟨U, hi, hfaith⟩ := exists_faithful_scalar_subrepresentation (F := F) σ hf
  exact (hbound U hi hfaith).trans
    ((subrepresentation_fixedCodim_le _ U A).trans_eq (fixedCodim_restrictScalars σ A))
end ReeF4.FixedSpaceEstimate
