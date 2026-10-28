module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Full marked G₂ presentation recognition in the original Chapter 12 preparation

Compatible A–F, torus and Weyl data on the independently marked split quotient
now produce the actual full G₂ amalgam comparison. Both endpoint maps and the
whole overlap use one constructed ambient equivalence composed with the supplied
source marking; genuine F.1.1 identifies the original common Sylow image.

This uses the proved finite presentation, including its separate binary kernel
argument. It assumes no unknown model map, simplicity or order. Constructing the
field-compatible source equations, generation and placements remains with the
split-recognition owner, and the earlier source premises remain with assembly.
Source: DGS, Groups and Graphs, p.224; Aschbacher–Smith 12.2.2, p.795, F.1.1–3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X F : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

include D in
/-- One full-model comparison retains all three representative formulas and
the actual original common Sylow, in either marked endpoint orientation. -/
theorem rankOne_g2_marked_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {shortIndex : Fin 2} (roots : RootData Q split F shortIndex)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ c : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) (flagAmalgam F shortIndex),
      (∀ a, (c.left a : Atlas.G2.Model F) =
        G2Presentation.quotientEquiv Q split roots (e.left a : X ⧸ Q.D)) ∧
      (∀ b, (c.middle b : Atlas.G2.Model F) =
        G2Presentation.quotientEquiv Q split roots (e.middle b : X ⧸ Q.D)) ∧
      (∀ a, (c.right a : Atlas.G2.Model F) =
        G2Presentation.quotientEquiv Q split roots (e.right a : X ⧸ Q.D)) ∧
      (MarkedLocal.sylowMap Q e
        (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1).range.map
          (G2Presentation.quotientEquiv Q split roots).toMonoidHom = Atlas.G2.unipotent := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact ⟨G2Presentation.comparison Q e split roots,
    G2Presentation.comparison_left_apply Q e split roots,
    G2Presentation.comparison_middle_apply Q e split roots,
    G2Presentation.comparison_right_apply Q e split roots,
    G2Presentation.source_sylow_image Q e hf split roots⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
