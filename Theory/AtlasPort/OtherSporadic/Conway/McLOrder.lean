/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLOrder.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLEndpointSequence

/-!
The McLaughlin order from the endpoint permutation exact sequence.
The two-element endpoint action and the known unordered-pair stabilizer order
give order 898128000 and the index 552 in Conway3.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLOrder.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
attribute [local instance] Classical.propDecidable

theorem mcl_endpoints_card : Nat.card McLEndpoints = 2 := by
  simp [McLEndpoints,Nat.card_eq_fintype_card,mcl_endpoints_ne]

theorem mcl_endpoint_permutation_card : Nat.card (Equiv.Perm McLEndpoints) = 2 := by
  rw [Nat.card_perm,mcl_endpoints_card]; rfl

theorem mcl_pair_order : Nat.card McLPairStabilizer = 1796256000 := point_stabilizer_card

theorem mcl_endpoint_index_product : 2*Nat.card McLModel = Nat.card McLPairStabilizer := by
  have hk := Nat.card_congr mclEndpointKernelEquiv.toEquiv
  have h := mclEndpointPermutation.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr mcl_endpoint_permutation_surjective,
    Subgroup.card_top,mcl_endpoint_permutation_card,hk] at h
  simpa only [mul_comm] using h

theorem mcl_order : Nat.card McLModel = 898128000 := by
  have h := mcl_endpoint_index_product
  rw [mcl_pair_order] at h
  omega

theorem mcl_order_factorization : Nat.card McLModel = 2^7*3^6*5^3*7*11 := by
  rw [mcl_order]
  norm_num

theorem mcl_co3_index_product : 552*Nat.card McLModel = Nat.card Model := by
  rw [mcl_order,card]; rfl

theorem mcl_pair_co3_index_product : 276*Nat.card McLPairStabilizer = Nat.card Model := by
  rw [mcl_pair_order,card]; rfl

end Atlas.Conway
