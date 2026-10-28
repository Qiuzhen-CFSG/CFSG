module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.VertexCorrection

/-!
# Core correction for the literal Chapter 12 M23 vertex

Use the whole reduced module from `rankOne_generic_input_of_many` to obtain
core-fixing automorphism correction on the original Ix. A vertex comparison
agreeing on the original core can then be corrected inside the edge fixer to
agree with the same heptad marking on the entire intersection. The original
Input, Preparation, perfect residual and both comparison orientations are
retained. The initial comparison and final ambient recognition are not proved
by these correction statements.

Source: Aschbacher--Smith 5.2.20(5), printed pp.656--657.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original local vertex intersection has only core conjugations fixing
its entire sixteen-core pointwise. -/
theorem rankOne_global_linear_exceptional_core_correction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ U : System G (G ⧸ (L ⊔ H : Subgroup G)),
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      ∀ α : MulAut (U.H ⊓ U.vertexGroup : Subgroup G),
        (∀ u : (J.pCoreIn 2).subgroupOf (U.H ⊓ U.vertexGroup), α u = u) →
        ∃ u : (J.pCoreIn 2).subgroupOf (U.H ⊓ U.vertexGroup),
          α = MulAut.conj (u : (U.H ⊓ U.vertexGroup : Subgroup G)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hcorr⟩ :=
    d.linear_nonmaximal_coset_core_correction hi hH hp E hm hE he hnonmax
  exact ⟨J,hJ,hKJ,U,hv,he0,hrigid,hcoreEdge,hcorr⟩

/-- Any initial vertex comparison agreeing on the original core and preserving
Ix and the edge fixer can be adjusted to agree with the same heptad marking on
all of Ix. Construction of the initial comparison remains a source obligation. -/
theorem rankOne_global_linear_exceptional_vertex_correction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer)
        (hUJ : U.H ≤ J),
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      ∀ β : U.vertexGroup ≃* pairStabilizer,
        ((U.H ⊓ U.vertexGroup).subgroupOf U.vertexGroup).map β.toMonoidHom =
          fourPairStabilizer.subgroupOf pairStabilizer →
        (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G), (r : G) ∈ J.pCoreIn 2 →
          (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
            (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) →
        (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
          (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) →
        ∃ β' : U.vertexGroup ≃* pairStabilizer,
          (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G),
            (β' ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
              (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) ∧
          ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
            (β' a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_vertex_correction hi hH hp E hm hE he hnonmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
