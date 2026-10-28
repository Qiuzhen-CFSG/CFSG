module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentAction
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.BinarySylow

/-!
# The source component stabilizer and involution centralizer

The point orbit in the component has order280 and stabilizer N(W) of
order11664, so the component stabilizer has order3265920. The actual
opposite SL₂(3) factor belongs to it because its two cubic generators
belong to the component. Together with the other factor and N(V), this
contains the full original involution centralizer by the source Frattini
decomposition. Consequently it contains an ambient Sylow two-subgroup.

Source: Aschbacher, *Sporadic Groups* (1994),45.5,45.10–45.11, pp.244,248.
The equality of this subgroup with G remains a global source obligation.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem componentStabilizer_card : Nat.card c.componentStabilizer = 3265920 := by
  classical
  let := c.conjugationAction
  let W : c.points := ⟨c.W, c.point_mem⟩
  let H := c.componentStabilizer
  have he : MulAction.orbit H W = {U : c.points | c.collinearity.Reachable W U} := by
    ext U
    constructor
    · rintro ⟨g, hg⟩
      change c.conjugatePoint W g.val = U at hg
      exact hg ▸ g.property
    · intro hU
      obtain ⟨g, hg⟩ := U.property
      have hp : c.conjugatePoint W g = U := Subtype.ext hg.symm
      have hgH : g ∈ H := by
        change c.collinearity.Reachable W (c.conjugatePoint W g)
        rw [hp]
        exact hU
      exact ⟨⟨g, hgH⟩, hp⟩
  have hs : MulAction.stabilizer H W = (normalizer (c.W : Set G)).subgroupOf H := by
    ext g
    change c.conjugatePoint W g.val = W ↔ g.val ∈ normalizer (c.W : Set G)
    exact ⟨fun hg => mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val hg),
      fun hg => Subtype.ext (mem_normalizer_iff_map_conj_eq.mp hg)⟩
  have hc : Nat.card (MulAction.stabilizer H W) = 11664 := by
    rw [hs, Nat.card_congr (subgroupOfEquivOfLe c.point_normalizer_le_componentStabilizer).toEquiv]
    exact c.point_normalizer_card
  have hi : (MulAction.stabilizer H W).index = 280 := by
    change Nat.card (H ⧸ MulAction.stabilizer H W) = 280
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H W), he]
    exact c.component_card
  have hh := (MulAction.stabilizer H W).index_mul_card
  rw [hi, hc] at hh
  exact hh.symm

theorem oppositeFactor_le_componentStabilizer : c.oppositeFactor ≤ c.componentStabilizer := by
  obtain ⟨Y, hYL, hY, hne, hgen, -⟩ := c.exists_complement_fixed_opposite_cubic
  have hreach : c.collinearity.Reachable ⟨c.W, c.point_mem⟩
      ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩ :=
    (c.reachable_iff_withinTwo _).mpr (Or.inr (Or.inr (c.opposite_cubic_distance_two hYL hY hne)))
  rw [← hgen]
  exact sup_le (c.W.le_normalizer.trans c.point_normalizer_le_componentStabilizer)
    (Y.le_normalizer.trans (c.component_point_normalizer_le hreach))

theorem core_le_componentStabilizer : core z ≤ c.componentStabilizer := by
  have hj : c.J ≤ c.componentStabilizer :=
    (le_sup_left.trans (c.complement_le.trans inf_le_right)).trans
      c.point_normalizer_le_componentStabilizer
  rw [← h.toCentralizerHypothesis.factorData.core_span h.involution]
  exact sup_le (le_sup_left.trans c.oppositeFactor_le_componentStabilizer)
    (le_sup_left.trans hj)

/-- The full original involution centralizer preserves the cubic component. -/
theorem centralizer_le_componentStabilizer : centralizer z ≤ c.componentStabilizer := by
  rw [h.centralizer_eq_core_sup_cubic_normalizer c.X (h.cubic_sylow_image_card P) (map_subtype_le _)]
  exact sup_le c.core_le_componentStabilizer
    ((inf_le_right.trans (CubicNormalizer.normalizer_normalizes_oddKernel c.X)).trans
      c.kernel_normalizer_le_componentStabilizer)

theorem exists_binarySylow_le_componentStabilizer :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ c.componentStabilizer ∧ Nat.card T = 128 := by
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨T, hT⟩ := R.exists_sylow_T h
  refine ⟨T, ?_, ?_⟩
  · rw [hT]
    exact R.T_le_centralizer.trans c.centralizer_le_componentStabilizer
  · rw [hT]
    exact R.T_card h

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
