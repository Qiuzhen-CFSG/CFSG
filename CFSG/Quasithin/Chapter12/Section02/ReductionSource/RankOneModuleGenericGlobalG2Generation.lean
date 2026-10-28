module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Generation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2LocalSylow

/-!
# The ambient G₂ completion for the original Chapter12 pair

The original two factors and their full normalizers generate G, using the
proved all-degree Sylow equality and full short-root centralizer bound.
Their compatible maps then give a faithful completion in this same G, with
both maps and the entire Borel overlap retained. No generation, Sylow-equality
or centralizer callback remains in these applications.

The concrete comparison and original uniqueness in Preparation remain inputs.
Exhaustive F.1.12 comparison, identification of the concrete completion and
final GlobalExit remain with the generic-global assembly.
Source: Aschbacher–Smith F.4.42–44, pp.295–296, and 5.3.3–4, p.659,
with the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual original factors generate G in every prepared G₂ case,
with S=T and the short-root centralizer premise both discharged. -/
theorem rankOne_global_g2_ambient_generation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      L ⊔ residual H = ⊤ :=
  d.g2_ambient_generation (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

/-- The supplied compatible maps give a faithful completion in the original
ambient group, with the full overlap identified exactly. -/
theorem rankOne_global_g2_ambient_completion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse (G := G),
      c.left = (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom ∧
      c.right = (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1).subtype.comp
        e.right.symm.toMonoidHom ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range :=
  d.g2_ambient_completion (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
