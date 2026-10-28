module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.CubicNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LinearCompletion

/-!
# Original generated linear completion at the Chapter 12 consumer

Use the whole reduced module through `rankOne_generic_input_of_many`, then
apply the source 5.2.16(1) recognition theorem. Its actual generated subgroup
is PSL₃(4), with both original parabolics and the whole Borel preserved. The
prepared whole residual and its inherited perfectness remain exactly the
source data. No extra normalizer, involution, or recognition input is needed.

Source: Aschbacher–Smith 5.2.16(1), printed p.655 (`refs/quasithin.pdf`).
This does not yet assert the field extension or the ambient M₂₃ GlobalExit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 5.2.16(1) applied to the literal whole reduced-module input. -/
theorem rankOne_global_linear_nonmaximal_generated_equiv
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
    ∃ e : (P ⊔ Q : Subgroup G) ≃* Matrix.PSL3Four.PSL,
      (((P.subgroupOf (P ⊔ Q)).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (Q.subgroupOf (P ⊔ Q)).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F) ∨
       ((Q.subgroupOf (P ⊔ Q)).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (P.subgroupOf (P ⊔ Q)).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F)) ∧
      ((P ⊓ Q).subgroupOf (P ⊔ Q)).map e.toMonoidHom = borel Matrix.PSL3Four.F := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_generated_equiv hi hH hp E hm hE he hnonmax
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
