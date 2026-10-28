module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.EdgeRigidity

/-!
# The literal Chapter 12 M23 coset-system rigidity

Specialize the actual source coset-system construction to the whole reduced
module supplied by `ChosenModule`. The output retains the original coset
action, identifies its vertex and edge stabilizers with L ∨ H and L, and
proves the pointwise automorphism rigidity of its local edge fixer.
Source: Aschbacher--Smith 5.2.19--5.2.22, printed pp.656--657.
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

/-- The exceptional linear row has its actual source coset graph and edge
fixer with proved rigidity under the hypotheses inherited by the real `ChosenModule` consumer. -/
theorem rankOne_global_linear_exceptional_rigid_coset_system
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
    ∃ U : System G (G ⧸ (L ⊔ H : Subgroup G)),
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hvertex,hedge,hUJ,hcore,hK,hHm,hMm,hIm,hvM,heM,hesM,horbit,ht,hrigid⟩ :=
    d.linear_nonmaximal_rigid_coset_system hi hH hp E hm hE he hnonmax
  exact ⟨U,hvertex,hedge,hrigid⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
