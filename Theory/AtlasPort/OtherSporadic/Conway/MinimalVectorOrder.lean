/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimalVectorOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumPairOrder
public import Theory.AtlasPort.OtherSporadic.Conway.SextetIsometry
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimalVectorOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem strict_overgroup_order (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) :
    Nat.card H = 196560 * 93150 * 1024 * 443520 := by
  let e : Fin 2 ↪ Omega := ⟨![((0,0),0),((0,0),1)],by decide⟩
  let x : LeechShell 4 := ⟨minimumPairPlus (e 0) (e 1),
    minimumPairPlus_norm _ _ (e.injective.ne (by decide))⟩
  let := strict_overgroup_minimum_pretransitive H hH
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),
    leech_minimal_shell_card,shell_stabilizer_eq,
    strict_overgroup_point_stabilizer_order H hH e] at hc
  exact hc.symm.trans (by norm_num)

theorem monomial_lt_full : monomialSubgroup < (⊤ : Subgroup LeechIsometryGroup) := by
  refine lt_of_le_of_ne le_top ?_
  intro he
  exact zeta_not_monomial (he ▸ Subgroup.mem_top zeta)

theorem leechIsometryGroup_order :
    Nat.card LeechIsometryGroup = 8315553613086720000 := by
  have h := strict_overgroup_order ⊤ monomial_lt_full
  rw [Subgroup.card_top] at h
  exact h.trans (by norm_num)

theorem leechIsometryGroup_order_minimal_pair (a : Omega) (b : Mathieu23Points a) :
    Nat.card LeechIsometryGroup = 196560 * 93150 * 2^10 * Nat.card (Mathieu22PointModel a b) := by
  rw [leechIsometryGroup_order,mathieu22_order]
  norm_num

theorem strict_overgroup_eq_full (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) : H = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [strict_overgroup_order H hH,leechIsometryGroup_order]

theorem monomial_maximal : IsCoatom monomialSubgroup := by
  refine ⟨ne_of_lt monomial_lt_full,?_⟩
  intro H hH
  exact strict_overgroup_eq_full H hH

theorem generatedConwayGroup_eq_full : generatedConwayGroup = ⊤ := by
  apply strict_overgroup_eq_full
  refine lt_of_le_of_ne le_sup_left ?_
  intro he
  have hz : zeta ∈ generatedConwayGroup :=
    (show Subgroup.closure {zeta} ≤ generatedConwayGroup from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton zeta))
  exact zeta_not_monomial (he ▸ hz)

end Atlas.Conway
