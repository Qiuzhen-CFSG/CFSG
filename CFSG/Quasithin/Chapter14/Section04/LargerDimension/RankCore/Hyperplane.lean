module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.Representation.BinaryHyperplaneRankObstruction

/-!
# The rank obstruction on the actual star image of D

The source bound [W,D] ≤ V₁ᵍ maps the quotient hyperplane W̃ into the
marked line Ṽ₂. Applying the involution-rank dichotomy to the actual star
image of the two-group D makes that image trivial. The resulting bound
D ≤ O₂(H) is obtained through the literal quotient map; the source geometric
centralizer calculation supplying the hyperplane bound remains explicit.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, first
paragraph of 14.4.7, printed pp.1008--1009.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Module Subgroup
variable {H V : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

/-- The rank obstruction gives D ≤ Q on the literal central quotient,
without assuming that all elements of D have order two. -/
theorem SourceAction.le_twoCore_of_hyperplane
    (d : SourceAction H U V) (D W V₂ : Subgroup H) (hD : IsPGroup 2 D)
    (hW : finrank (ZMod 2) (V ⧸ d.image W) = 1)
    (hV₂ : finrank (ZMod 2) (d.image V₂) = 1)
    (hm : ∀ a ∈ D, (d.image W).map
      (d.representation (QuotientGroup.mk' (pCore 2 H) a) - LinearMap.id) ≤ d.image V₂)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.movedRank a ∨ (d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a)) :
    D ≤ pCore 2 H := by
  let π := QuotientGroup.mk' (pCore 2 H)
  have hbot : D.map π = ⊥ :=
    Representation.BinaryHyperplaneRankObstruction.twoSubgroup_eq_bot
      d.representation (D.map π) (hD.map π) (d.image W) (d.image V₂) hW hV₂
      (by rintro _ ⟨a, ha, rfl⟩; exact hm a ha) hrank
  intro a ha
  have hmem : π a ∈ D.map π := mem_map_of_mem π ha
  rw [hbot] at hmem
  exact (QuotientGroup.eq_one_iff a).mp hmem

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
