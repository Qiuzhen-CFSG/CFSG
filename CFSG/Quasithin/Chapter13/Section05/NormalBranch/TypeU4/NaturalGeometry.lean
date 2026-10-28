module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceComponent
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeAdjacency
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.StrongEmbedding

/-!
# Cubic geometry from the original natural normal branch

The natural flag now constructs the returning plane and its conjugator.
Thus the original13.5.15 conclusions and M=L branch supply IsType and
the actual cubic graph, complete distance-two sphere and component group.
The full Bender–Suzuki source theorem excludes strong embedding of this
literal component subgroup. The neighboring/opposite adjacency formula
is retained for the remaining local comparison in Asc9445.11.

No returning conjugator, core-intersection identity, type, connectedness
or recognition conclusion is assumed here. The original natural setup,
13.5.15 conclusions and branch selection remain earlier source inputs.
Source: Aschbacher–Smith,13.5.16, pp.921–922; Asc94,45.10–45.11, pp.248–249.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
open Theory.GroupTheory.Recognition
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}

theorem cubic_geometry_of_natural_normal_branch
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M = D.L)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (P : Sylow 3 (UnitaryFourThree.centralizer z)) :
    ∃ ht : UnitaryFourThree.IsType z,
      ∃ c : UnitaryFourThree.CubicGeometry.SourceConfiguration ht P,
        Nat.card c.componentStabilizer = 3265920 ∧ D.H ≤ c.componentStabilizer ∧
        ¬BenderSuzuki.IsStronglyEmbedded c.componentStabilizer ∧
        Nat.card {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} = 243 ∧
        (∀ U : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 →
          Nonempty ((c.W ⊔ U.val : Subgroup G) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) ∧
        (∃ Y : Subgroup G, Y ≤ c.oppositeFactor ∧ Nat.card Y = 3 ∧ Y ≠ c.W ∧
          c.K ≤ normalizer (Y : Set G) ∧
          ∀ a ∈ c.D, Y.conjBy a ∈ c.neighbors c.otherAxis ↔ a ∈ c.V ⊓ c.D) := by
  let ht := isType_of_natural_normal_branch d h b hM z hz hz1
  obtain ⟨c⟩ := ht.original_cubic_source_configuration P
  obtain ⟨Y, hYL, hY, hne, -, hK⟩ := c.exists_complement_fixed_opposite_cubic
  exact ⟨ht, c, c.componentStabilizer_card,
    (centralizer_eq h b z hz hz1) ▸ c.centralizer_le_componentStabilizer,
    c.componentStabilizer_not_stronglyEmbedded, c.distance_two_sphere_card,
    fun _ hU => c.distance_two_pair_model hU, Y, hYL, hY, hne, hK,
    fun a ha => c.opposite_neighbor_iff_mem_kernel_intersection hYL hY hne a ha⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
