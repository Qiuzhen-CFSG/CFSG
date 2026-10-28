module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.RecognitionFromVertex

/-!
# The literal Chapter 12 recognition reduction to the initial vertex marking

Specialize the source input to the whole reduced module via
`rankOne_generic_input_of_many`. On the original constructed coset system, a
vertex comparison preserving Ix and L and agreeing with the fixed heptad map on
O2(J) now gives the actual M23 disjunct of GlobalExit. This consumes the full
source correction, similarity and ambient recognition chain.

The initial comparison remains an explicit premise of the implication in the
conclusion; this is not the unconditional nonmaximal linear endpoint. Both
amalgam orientations, the original Preparation and perfect residual are retained.
Source: Aschbacher--Smith 5.2.20(5) and Theorem 5.2.10, printed pp.656--658.
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

/-- On the original constructed system, a core-compatible vertex comparison
suffices for the actual M23 disjunct. The construction of that comparison remains
an obligation of the unconditional nonmaximal linear branch. -/
theorem rankOne_global_linear_nonmaximal_recognition_reduction
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
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (hUJ : U.H ≤ J),
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
      ∀ β : U.vertexGroup ≃* pairStabilizer,
        ((U.H ⊓ U.vertexGroup).subgroupOf U.vertexGroup).map β.toMonoidHom =
          fourPairStabilizer.subgroupOf pairStabilizer →
        (∀ r : (U.H ⊓ U.vertexGroup : Subgroup G), (r : G) ∈ J.pCoreIn 2 →
          (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
            (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23)) →
        (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
          (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) →
        RankOneModule.GlobalExit G := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨J,hJ,hKJ,U,ζ,hUJ,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hrec⟩ :=
    d.linear_nonmaximal_recognition_reduction hi hH hp E hm hE he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,?_⟩
  intro β hβR hβcore hβedge
  obtain ⟨e,_⟩ := hrec β hβR hβcore hβedge
  exact Or.inr (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
