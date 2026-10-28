module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Models

/-!
# Finite calculations for the marked binary parabolic

The two independent translations distinguish the point four-group from its
line counterpart. A cubic Levi element detects the action on the quotient.
All calculations use the actual determinant-one matrices and kernel reduction.

Source: Aschbacher–Smith 13.8.21(1), printed p.957.
-/

@[expose] public section
namespace Matrix.PSL3Two.MarkedAutomorphisms
open Subgroup

def cubic : SL := ⟨!![1,0,0; 0,0,1; 0,1,1], by decide +kernel⟩

theorem cubic_mem : cubic ∈ pointA := by decide +kernel

theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel

theorem translations_mem : Bruhat.upper 1 ∈ pointA ∧ Bruhat.upper 2 ∈ pointA := by
  decide +kernel

theorem pointA_le : pointA ≤ pointParabolicSL := by
  intro g hg
  exact (mem_pointParabolicSL_iff g).mpr ⟨hg.1, hg.2.1⟩

theorem pointV_le : pointV ≤ pointA := by
  intro g hg
  exact ⟨hg.2.1, hg.2.2.1, Or.inl hg.2.2.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem pointA_conj : ∀ g : SL, g ∈ pointParabolicSL → ∀ a : SL, a ∈ pointA →
    g * a * g⁻¹ ∈ pointA := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem parabolic_square : ∀ g : SL, g ∈ pointParabolicSL → g ^ 2 ∈ pointA := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cubic_factor : ∀ g : SL, g ∈ pointA →
    g ^ 3 = 1 ∨ (cubic⁻¹ * g) ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem pointV_conj : ∀ g : SL, g ∈ pointA → ∀ a : SL, a ∈ pointV →
    g * a * g⁻¹ ∈ pointV := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem pointV_square : ∀ g : SL, g ∈ pointV → g ^ 2 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem pointA_order_test : ∀ g : SL, g ∈ pointA → g ∈ pointV ∨ g ^ 3 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem card_pointA : Nat.card pointA = 12 := by
  change Nat.card {g : SL // pointResidualPred g} = 12
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem card_pointV : Nat.card pointV = 4 := by
  change Nat.card {g : SL // pointCorePred g} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem graph_not_inner_test : ∀ g : SL,
    ¬ (g * Bruhat.upper 1 = diagram (Bruhat.upper 1) * g ∧
       g * Bruhat.upper 2 = diagram (Bruhat.upper 2) * g) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem inner_preserving_test : ∀ g : SL,
    g * Bruhat.upper 1 * g⁻¹ ∈ pointA →
    g * Bruhat.upper 2 * g⁻¹ ∈ pointA → g ∈ pointParabolicSL := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem outer_exclusion_test : ∀ g : SL,
    ¬ (g * diagram (Bruhat.upper 1) * g⁻¹ ∈ pointA ∧
       g * diagram (Bruhat.upper 2) * g⁻¹ ∈ pointA) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem quotient_fixer_test : ∀ g : SL, g ∈ pointParabolicSL →
    g * cubic * g⁻¹ * cubic⁻¹ ∈ pointV → g ∈ pointA := by decide +kernel

end Matrix.PSL3Two.MarkedAutomorphisms
