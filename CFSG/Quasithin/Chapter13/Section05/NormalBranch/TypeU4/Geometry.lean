module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceGeometry

/-!
# The original Chapter 13 cubic geometry

The first branch of 13.5.16 supplies an actual involution centralizer and
returning plane. Its original type construction feeds the Asc94 cubic
source configuration. The graph is the literal conjugacy orbit of the
constructed cubic subgroup, its distance-two sphere has order 243 and
its component has order 280. Every opposite pair generates SL₂(3), and
the actual odd subgroup acts regularly on that sphere.

The nine conclusions of 13.5.15 and the selected returning-plane equation
remain the earlier source inputs. No type or recognition conclusion is
assumed by this consumer.
Source: Aschbacher–Smith, 13.5.15–16, pp.919–922;
Aschbacher, *Sporadic Groups* (1994), 45.10, pp.247–248.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
open Theory.GroupTheory.Recognition
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {M : Subgroup G} {g : G}

theorem cubic_geometry_of_returning_plane (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (hM : M = D.L) (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (V₂ : Subgroup G) (hline : D.V₁ ≤ V₂) (hseed : V₂ ≤ D.Vplus)
    (hfour : Nat.card V₂ = 4) (y : G)
    (hy : y ∈ normalizer (V₂ : Set G)) (hyH : y ∉ D.H)
    (hpair : D.UH ⊓ UnitaryFourThree.conjugate D.UH y = V₂)
    (P : Sylow 3 (UnitaryFourThree.centralizer z)) :
    ∃ ht : UnitaryFourThree.IsType z,
      ∃ c : UnitaryFourThree.CubicGeometry.SourceConfiguration ht P,
        (∀ U : c.points, Nat.card (c.collinearity.neighborSet U) = 36) ∧
        Nat.card {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} = 243 ∧
        Nat.card {U : c.points // c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U} = 280 ∧
        (∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
          Nonempty ((c.W ⊔ U.val : Subgroup G) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) ∧
        (∃ Y : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ Y = 2 ∧
          normalizer (c.W : Set G) ⊓ normalizer (Y.val : Set G) = c.K ∧
          ∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
            ∃! d : c.D, U.val = Y.val.conjBy d.val) := by
  let ht := isType_of_returning_plane h b hM z hz hz1 V₂ hline hseed hfour y hy hyH hpair
  obtain ⟨c⟩ := ht.original_cubic_source_configuration P
  exact ⟨ht, c, c.collinearity_neighbor_card, c.distance_two_sphere_card, c.component_card,
    fun _ hU => c.distance_two_pair_model hU, c.exists_regular_distance_two⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
