module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.NormalizerCompatibility

/-!
# Chapter 12 recognition reduced to pointwise core alignment

The literal source construction gives a vertex comparison carrying the original
edge fixer, linear subgroup, full exceptional core and H to their native images.
If it agrees with the same heptad marking on the entire core, self-centralization
determines the image of the whole Ix. Core correction and uniqueness-system
recognition then give the actual M23 disjunct of GlobalExit.

Pointwise core agreement remains an explicit condition in the conclusion.
This is a checked reduction, not unconditional source 5.2.10. The whole reduced
module and both compatible linear-amalgam orientations are retained.
Source: Aschbacher--Smith 5.2.20(5) and 5.2.10, printed pp.656--658.
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

/-- The constructed source vertex map needs only pointwise core alignment
for the actual M23 disjunct; preservation of Ix is then a consequence. -/
theorem rankOne_global_linear_nonmaximal_coset_core_recognition_reduction
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
        pointwisePairStabilizer ∧
      ((J.pCoreIn 2).subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadKernelAmbient.subgroupOf pairStabilizer ∧
      (H.subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadStabilizer.subgroupOf pairStabilizer ∧
      ((∀ (u : U.vertexGroup) (hu : (u : G) ∈ J.pCoreIn 2),
        (β u : Sporadic.Mathieu.M23) =
          (ζ ⟨u,pCoreIn_le 2 J hu⟩ : Sporadic.Mathieu.M23)) →
        RankOneModule.GlobalExit G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hβedge,hβlinear,hβU,hβH,hrec⟩ :=
    d.linear_nonmaximal_coset_core_recognition_reduction hi hH hp F hm hF he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hβedge,hβlinear,hβU,hβH,?_⟩
  intro hagree
  obtain ⟨e,_⟩ := hrec hagree
  exact Or.inr (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
