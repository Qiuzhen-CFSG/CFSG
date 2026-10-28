/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSLocalOrbits

/-!
Order and transitivity of the concrete Higman–Sims model.
The Conway3 order saturates the independent side and graph orbit bounds, giving order 44352000.

Source: Gerald Höhn, `Atlas/Conway/HSOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

abbrev HSSideStabilizer := stabilizer Atlas.Sporadic.Conway3.Model hsBaseSide

def hsSideStabilizerEquiv : HSSideStabilizer ≃* HSModel where
  toFun g := ⟨g.val,congrArg Subtype.val g.prop⟩
  invFun g := ⟨g.val,Subtype.ext g.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem hs_side_orbit_stabilizer :
    Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide)*Nat.card HSModel =
      Nat.card Atlas.Sporadic.Conway3.Model := by
  have he := Nat.card_congr (orbitProdStabilizerEquivGroup Atlas.Sporadic.Conway3.Model hsBaseSide)
  rw [Nat.card_prod,Nat.card_congr hsSideStabilizerEquiv.toEquiv] at he
  exact he

theorem hs_graph_orbit_stabilizer :
    Nat.card (orbit HSModel hsBaseGraphPoint)*443520 = Nat.card HSModel := by
  have he := Nat.card_congr (orbitProdStabilizerEquivGroup HSModel hsBaseGraphPoint)
  rw [Nat.card_prod,hs_graph_stabilizer_card] at he
  exact he

/-- Both independently bounded orbits are saturated by the previously proved Co3 order. -/
theorem hs_saturated_orbit_bounds :
    Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide) = 11178 ∧
    Nat.card (orbit HSModel hsBaseGraphPoint) = 100 := by
  have hb : Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide) ≤ 11178 := by
    rw [← hs_sides_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hc : Nat.card (orbit HSModel hsBaseGraphPoint) ≤ 100 := by
    rw [← hs_graph_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have he := hs_side_orbit_stabilizer
  rw [← hs_graph_orbit_stabilizer,Atlas.Sporadic.Conway3.card,← Nat.mul_assoc] at he
  have hp : Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide)*
      Nat.card (orbit HSModel hsBaseGraphPoint) = 1117800 := by
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 443520) he
  have hb' := Nat.mul_le_mul_left (Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide)) hc
  have hc' := Nat.mul_le_mul_right (Nat.card (orbit HSModel hsBaseGraphPoint)) hb
  rw [hp] at hb' hc'
  clear he
  constructor <;> omega

theorem hs_order : Nat.card HSModel = 44352000 := by
  have he := hs_graph_orbit_stabilizer
  rw [hs_saturated_orbit_bounds.2] at he
  exact he.symm

theorem hs_order_factored : Nat.card HSModel = 2^9*3^2*5^3*7*11 := by
  rw [hs_order]
  norm_num

theorem hs_side_orbit_univ : orbit Atlas.Sporadic.Conway3.Model hsBaseSide = Set.univ := by
  apply (Set.eq_univ_iff_ncard _).mpr
  change Nat.card (orbit Atlas.Sporadic.Conway3.Model hsBaseSide) = Nat.card HSSides
  rw [hs_saturated_orbit_bounds.1,hs_sides_card]

theorem hs_graph_orbit_univ : orbit HSModel hsBaseGraphPoint = Set.univ := by
  apply (Set.eq_univ_iff_ncard _).mpr
  change Nat.card (orbit HSModel hsBaseGraphPoint) = Nat.card HSGraphPoints
  rw [hs_saturated_orbit_bounds.2,hs_graph_card]

theorem hs_sides_transitive : IsPretransitive Atlas.Sporadic.Conway3.Model HSSides :=
  (isPretransitive_iff_orbit_eq_univ hsBaseSide).mpr hs_side_orbit_univ

theorem hs_graph_transitive : IsPretransitive HSModel HSGraphPoints :=
  (isPretransitive_iff_orbit_eq_univ hsBaseGraphPoint).mpr hs_graph_orbit_univ

theorem hs_conway3_order_identity : 11178*Nat.card HSModel = Nat.card Atlas.Sporadic.Conway3.Model := by
  rw [← hs_saturated_orbit_bounds.1]
  exact hs_side_orbit_stabilizer

theorem hs_mathieu22_order_identity : Nat.card HSModel = 100*Nat.card HSMathieuModel := by
  rw [hs_order,mathieu22_order]

end Atlas.Conway
