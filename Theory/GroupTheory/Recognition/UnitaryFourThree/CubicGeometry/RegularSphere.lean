module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.DistanceTwo

/-!
# The original regular action and source consumer

The full distance-two sphere is the orbit of the selected opposite cubic.
Its trivial D-stabilizer gives a unique actual conjugating element of D
for every point of that sphere. The final consumer constructs the source
configuration from IsType and retains its original subgroups throughout.

Source: Aschbacher, *Sporadic Groups* (1994), 45.10(6)–(7), p.248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem opposite_odd_conjugation_injective {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    Function.Injective (fun d : c.D => Y.conjBy d.val) := by
  intro d d' he
  change Y.conjBy d.val = Y.conjBy d'.val at he
  have hdD : d'.val⁻¹ * d.val ∈ c.D := c.D.mul_mem (c.D.inv_mem d'.property) d.property
  have hdN : d'.val⁻¹ * d.val ∈ normalizer (Y : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Y.conjBy (d'.val⁻¹ * d.val) = Y
    rw [conjBy_mul, he, conjBy_inv]
  have hd0 : d'.val⁻¹ * d.val ∈ (⊥ : Subgroup G) :=
    c.opposite_cubic_odd_stabilizer hYL hY hne ▸ ⟨hdD, hdN⟩
  exact Subtype.ext (inv_mul_eq_one.mp (mem_bot.mp hd0)).symm

/-- Regularity is stated using the literal subgroup and actual conjugation. -/
theorem exists_regular_distance_two :
    ∃ Y : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ Y = 2 ∧
      normalizer (c.W : Set G) ⊓ normalizer (Y.val : Set G) = c.K ∧
      (∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
        ∃! d : c.D, U.val = Y.val.conjBy d.val) := by
  obtain ⟨Y, hYL, hY, hne, -, hK⟩ := c.exists_complement_fixed_opposite_cubic
  refine ⟨⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩,
    c.opposite_cubic_distance_two hYL hY hne,
    c.opposite_cubic_common_normalizer hYL hY hne hK, ?_⟩
  intro U hU
  obtain ⟨d, hd, he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hU
  refine ⟨⟨d, hd⟩, he, ?_⟩
  intro d' he'
  exact c.opposite_odd_conjugation_injective hYL hY hne (he'.symm.trans he)

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Original input produces the actual source graph, its complete distance-two
sphere, regular odd action and SL₂(3) opposite-pair subgroups. -/
theorem original_cubic_distance_two (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃ c : CubicGeometry.SourceConfiguration h P,
      (∀ U : c.points, Nat.card (c.collinearity.neighborSet U) = 36) ∧
      Nat.card {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} = 243 ∧
      (∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
        Nat.card (c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩ U) = 4 ∧
        Nonempty ((c.W ⊔ U.val : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) ∧
      (∃ Y : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ Y = 2 ∧
        normalizer (c.W : Set G) ⊓ normalizer (Y.val : Set G) = c.K ∧
        ∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
          ∃! d : c.D, U.val = Y.val.conjBy d.val) := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c, c.collinearity_neighbor_card, c.distance_two_sphere_card,
    fun _ hU => ⟨c.distance_two_common_neighbors_card hU, c.distance_two_pair_model hU⟩,
    c.exists_regular_distance_two⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
