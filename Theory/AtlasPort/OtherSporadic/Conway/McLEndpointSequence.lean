/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLEndpointSequence.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLEndpointInterchange
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PairRestrictionSurjective

/-!
The endpoint permutation exact sequence for the triangle stabilizer.
Endpoint interchange makes the restriction surjective, and its kernel is
identified with the actual pointwise stabilizer by subgroup equivalences.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLEndpointSequence.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
open scoped Pointwise
attribute [local instance] Classical.propDecidable

abbrev McLEndpoints := ({mclEndpoint,mclOtherEndpoint} : Set leech)

def mclPairEquiv : McLPairStabilizer ≃*
    Atlas.GroupTheory.PairStabilizer (G := Model) mclEndpoint mclOtherEndpoint :=
  MulEquiv.subgroupCongr mcl_pair_stabilizer_eq

def mclEndpointPermutation : McLPairStabilizer →* Equiv.Perm McLEndpoints :=
  (Atlas.GroupTheory.pairRestrictionHom mclEndpoint mclOtherEndpoint).comp mclPairEquiv.toMonoidHom

theorem mcl_endpoint_permutation_surjective : Function.Surjective mclEndpointPermutation := by
  change Function.Surjective ((Atlas.GroupTheory.pairRestrictionHom (G := Model)
    mclEndpoint mclOtherEndpoint) ∘ mclPairEquiv)
  apply Function.Surjective.comp _ mclPairEquiv.surjective
  apply Atlas.GroupTheory.pairRestriction_surjective_of_moves _ _ mcl_endpoints_ne
  obtain ⟨g,hg⟩ := not_forall.mp mcl_endpoint_not_fixed
  exact ⟨mclPairEquiv g,hg⟩

/-- Equality of actual pointwise stabilizers; fixing x and a also fixes x-a. -/
theorem mcl_fixing_pair_eq : fixingSubgroup Model McLEndpoints =
    MulAction.stabilizer Model mclEndpoint := by
  ext g
  constructor
  · intro hg
    exact hg ⟨mclEndpoint,Or.inl rfl⟩
  · intro hg y
    change g.val.val y.val = y.val
    rcases y.prop with hy | hy
    · rw [hy]; exact hg
    · rw [show y.val = mclOtherEndpoint from hy]
      exact mcl_fixes_other_endpoint ⟨g,hg⟩

def mclKernelPairEquiv : mclEndpointPermutation.ker ≃*
    (Atlas.GroupTheory.pairRestrictionHom (G := Model) mclEndpoint mclOtherEndpoint).ker where
  toFun g := ⟨mclPairEquiv g.val,g.prop⟩
  invFun g := ⟨mclPairEquiv.symm g.val,by
    change (Atlas.GroupTheory.pairRestrictionHom mclEndpoint mclOtherEndpoint)
      (mclPairEquiv (mclPairEquiv.symm g.val)) = 1
    rw [mclPairEquiv.apply_symm_apply]; exact g.prop⟩
  left_inv g := Subtype.ext (mclPairEquiv.symm_apply_apply _)
  right_inv g := Subtype.ext (mclPairEquiv.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def mclEndpointKernelEquiv : mclEndpointPermutation.ker ≃* McLModel :=
  mclKernelPairEquiv.trans
    ((Atlas.GroupTheory.pairRestrictionKernelEquiv mclEndpoint mclOtherEndpoint mcl_endpoints_ne).trans
      (MulEquiv.subgroupCongr mcl_fixing_pair_eq))

end Atlas.Conway
