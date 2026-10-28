module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo
public import Mathlib.LinearAlgebra.Projection

/-!
# Coordinates for a split index-two restriction

The complementary subrepresentations give an actual linear sum equivalence
and an equivariant projection onto the left constituent. Its dimension is
strictly smaller than the whole space since the right constituent is nonzero.
These are the coordinate maps used to identify the split alternative in
Aschbacher–Smith, proof of 13.8.25, printed pp.959–960 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
namespace RestrictionSplit
variable {F H U : Type*} [Field F] [Group H] [AddCommGroup U] [Module F U]
  {ρ : Representation F H U} {K : Subgroup H} (d : RestrictionSplit ρ K)

theorem complementary_submodules : IsCompl d.left.toSubmodule d.right.toSubmodule := by
  constructor
  · exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule d.complementary.inf_eq_bot)
  · exact codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule d.complementary.sup_eq_top)

noncomputable def sumEquiv : (d.left.toSubmodule × d.right.toSubmodule) ≃ₗ[F] U :=
  d.left.toSubmodule.prodEquivOfIsCompl d.right.toSubmodule d.complementary_submodules

@[simp] theorem sumEquiv_apply (x : d.left × d.right) : d.sumEquiv x = (x.1 : U) + x.2 := rfl

theorem sumEquiv_intertwines (k : K) (x : d.left × d.right) :
    d.sumEquiv (d.left.toRepresentation k x.1, d.right.toRepresentation k x.2) =
      ρ k (d.sumEquiv x) := (map_add (ρ k) _ _).symm

noncomputable def leftProjection : U →ₗ[F] d.left.toSubmodule :=
  d.left.toSubmodule.projectionOnto d.right.toSubmodule d.complementary_submodules

@[simp] theorem leftProjection_left (v : d.left.toSubmodule) : d.leftProjection v = v :=
  Submodule.projectionOnto_apply_left _ _

@[simp] theorem leftProjection_right (v : d.right.toSubmodule) : d.leftProjection v = 0 :=
  Submodule.projectionOnto_apply_right _ _

theorem leftProjection_intertwines (k : K) (v : U) :
    d.leftProjection (ρ k v) = d.left.toRepresentation k (d.leftProjection v) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := d.sumEquiv.surjective v
  simp only [sumEquiv_apply, map_add]
  change d.leftProjection (d.left.toRepresentation k x : U) +
    d.leftProjection (d.right.toRepresentation k y : U) = _
  simp

theorem apply_swapper_mem_right (v : d.left.toSubmodule) : ρ d.swapper v ∈ d.right := by
  change ρ d.swapper v ∈ d.right.toSubmodule
  rw [← d.map_left]
  exact ⟨v, v.property, rfl⟩

theorem finrank_left_lt [FiniteDimensional F U] :
    Module.finrank F d.left.toSubmodule < Module.finrank F U := by
  have hi : IsIrreducible d.right.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom _).mpr d.right_atom
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial d.right.toRepresentation
  have hpos := Module.finrank_pos (R := F) (M := d.right.toSubmodule)
  have he := Submodule.finrank_add_eq_of_isCompl d.complementary_submodules
  change Module.finrank F d.left.toSubmodule + Module.finrank F d.right.toSubmodule = _ at he
  omega

end RestrictionSplit
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
