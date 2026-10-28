module

public import Theory.Representation.EndFieldRep
public import Mathlib.RepresentationTheory.Invariants

/-!
# Invariant Dimensions over the Endomorphism Field

For a finite-dimensional irreducible representation over a finite field F,
let E be its existing Schur endomorphism field. The F-dimension of invariants
under any subgroup is [E:F] times the E-dimension of invariants in the actual
endomorphism-field representation. The acting group and subgroup need not
be finite.

The existing asModuleEquiv restricts to an F-linear equivalence of the two
invariant subspaces: its definition already intertwines the original action
with endFieldRep. The invariant subtype inherits the same scalar tower, so
the standard finrank multiplication theorem proves the formula without
replacing any field, module, or action instance.

This is the scalar-restriction step in the minimal faithful dimension case
of Alperin--Brauer--Gorenstein II.4, Lemma 18(ii), article pp. 45--46.
-/

open scoped MonoidAlgebra

namespace Representation

variable {F G V : Type*} [Field F] [Finite F] [Group G] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ρ : Representation F G V) [ρ.IsIrreducible]

private noncomputable def endFieldInvariantsEquiv (P : Subgroup G) :
    (Representation.invariants (ρ.endFieldRep.comp P.subtype)) ≃ₗ[F]
      (Representation.invariants (ρ.comp P.subtype)) where
  toFun v := ⟨ρ.asModuleEquiv v, by
    intro g
    have h := v.property g
    exact congrArg ρ.asModuleEquiv h⟩
  invFun v := ⟨ρ.asModuleEquiv.symm v, by
    intro g
    have h := v.property g
    exact congrArg ρ.asModuleEquiv.symm h⟩
  left_inv v := Subtype.ext (ρ.asModuleEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (ρ.asModuleEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add ρ.asModuleEquiv (x : ρ.asModule) (y : ρ.asModule))
  map_smul' a v := Subtype.ext (map_smul ρ.asModuleEquiv a (v : ρ.asModule))

public theorem finrank_invariants_eq_endField_mul (P : Subgroup G) :
    Module.finrank F (Representation.invariants (ρ.comp P.subtype)) =
      Module.finrank F (Module.End F[G] ρ.asModule) *
        Module.finrank (Module.End F[G] ρ.asModule) (Representation.invariants (ρ.endFieldRep.comp P.subtype)) := by
  rw [Module.finrank_mul_finrank F (Module.End F[G] ρ.asModule)]
  exact (endFieldInvariantsEquiv ρ P).finrank_eq.symm

end Representation
