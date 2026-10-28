module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LinearCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.FieldExtension

/-!
# The original field extension at the Chapter 12 consumer

The whole reduced-module input specializes source 5.2.16(2). Its actual
extension by the original T is the entrywise-Frobenius extension of PSL₃(4),
with both parabolics, the full Borel and the original linear inclusion retained.
Source: Aschbacher–Smith 5.2.16(2), printed p.655 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 5.2.16(2) for the literal whole reduced-module input. -/
theorem rankOne_global_linear_nonmaximal_field_extension
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
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
    let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let C := P ⊔ Q
    ∃ (e : C ≃* Matrix.PSL3Four.PSL)
      (f : (C ⊔ (T : Subgroup G) : Subgroup G) ≃* Matrix.PSL3Four.FieldExtension),
      (((P.subgroupOf C).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (Q.subgroupOf C).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F) ∨
       ((Q.subgroupOf C).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (P.subgroupOf C).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F)) ∧
      ((P ⊓ Q).subgroupOf C).map e.toMonoidHom = borel Matrix.PSL3Four.F ∧
      ∀ c : C, f ⟨c,mem_sup_left c.property⟩ = Matrix.PSL3Four.linearInclusion (e c) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_field_extension hi hH hp E hm hE he hnonmax
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
