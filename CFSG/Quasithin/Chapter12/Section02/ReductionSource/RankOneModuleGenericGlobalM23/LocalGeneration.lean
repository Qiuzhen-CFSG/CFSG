module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.FieldExtension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LocalGeneration

/-!
# The original four-set local generation at Chapter 12

Apply the same-marking coset construction to the literal whole reduced-module
input. Both edge-stabilizer conventions and the local generation identity
retain the original action on G/(L ∨ H).
Source: Aschbacher–Smith 5.2.19(3–4), the setwise clause of 5.2.20(3),
5.2.21, and 5.2.22, printed pp.656–657 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry Theory.GroupTheory.GraphUniquenessSystem
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The source local generation identity with all three stabilizer markings. -/
theorem rankOne_global_linear_exceptional_coset_local_generation
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
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : ∃ (ζ : J ≃* heptadStabilizer) (I : Subgroup J) (t : J),
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      I.map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧ t ∈ I ∧
      let x0 := ((1 : G) : G ⧸ (L ⊔ H : Subgroup G))
      let y0 := t • x0
      t • y0 = x0 ∧ x0 ≠ y0 ∧
      (I ⊓ MulAction.stabilizer J x0).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      (I ⊓ edgeFixer J x0 y0).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      (I ⊓ edgeStabilizer J x0 y0).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (I.map J.subtype ⊓ edgeStabilizer G x0 y0) ⊔
        (I.map J.subtype ⊓ MulAction.stabilizer G x0) = I.map J.subtype ∧
      I.map J.subtype ⊔ (L ⊔ H) = ⊤ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_exceptional_coset_local_generation hi hH hp E hm hE he hJ hKJ
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
