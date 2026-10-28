module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.VertexCoordinates

/-!
# Original vertex coordinates in the literal Chapter 12 branch

Use the whole reduced module from `rankOne_generic_input_of_many`, retaining
the original prepared whole residual and compatible linear amalgam. The same
source coset system and heptad marking now have an actual vertex equivalence
with the native pair stabilizer, carrying L to the native edge fixer and the
whole generated linear subgroup to the pointwise pair stabilizer.

The remaining agreement on Ix and its sixteen-core is not assumed or claimed.
Consequently this intermediate construction does not yet assert GlobalExit.
Source: Aschbacher--Smith 5.2.16, 5.2.18 and 5.2.20(5), printed pp.655--657.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Coordinates on the literal original coset vertex, together with the same
fixed heptad and local stabilizer markings. -/
theorem rankOne_global_linear_nonmaximal_coset_vertex_coordinates
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (_hUJ : U.H ≤ J)
        (β : U.vertexGroup ≃* pairStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
        (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) ∧
      ((L ⊔ residual H).subgroupOf U.vertexGroup).map β.toMonoidHom =
        pointwisePairStabilizer := by
  exact d.linear_nonmaximal_coset_vertex_coordinates
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnonmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
