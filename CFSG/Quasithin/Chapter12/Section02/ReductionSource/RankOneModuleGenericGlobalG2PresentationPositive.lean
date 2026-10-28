module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Positive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# The positive G₂ presentation in the original Chapter 12 preparation

The actual prepared pair supplies genuine F.1.1. On its independently marked
finite quotient, compatible A–F roots therefore give a surjection from the
concrete G₂ unipotent subgroup to the original S = O₂(N_G(L) ∩ H).
Both endpoint formulas use the supplied original/geometric marking, and
positive collection bounds the order of this same original S by q⁶.

The source field, the root equations and the quotient marking remain inputs
of the split-recognition owner. This is the positive part of the DGS Theorem D
comparison, not a full G₂ comparison or GlobalExit.
Source: DGS, Groups and Graphs, p.224; Aschbacher–Smith, 12.2.2, p.795,
and the original local-pair construction in F.1.1–3, pp.259–261.
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
/-- The literal original Sylow is a quotient of the proved positive presentation;
its images in both original endpoints carry exactly the same root parameters. -/
theorem rankOne_g2_positive_presentation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (roots : PositiveRoots F (X ⧸ Q.D)) (rels : roots.CharTwoRelations)
    (hU : roots.generated = split.U)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ f : Atlas.G2.unipotent (K := F) →* Global.sourceS L H,
      Function.Surjective f ∧
      (∀ (i : Fin 2) (t : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv t)
        MarkedLocal.endpointMap Q e i
          ⟨s, (show Global.sourceS L H ≤
            ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i from
              le_sup_right.trans le_sup_left) s.property⟩ = roots.product t) ∧
      Nat.card (Global.sourceS L H) ≤ Nat.card F ^ 6 := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact ⟨G2Presentation.sourceSylowHom Q split roots rels hU e hf,
    G2Presentation.sourceSylowHom_surjective Q split roots rels hU e hf,
    G2Presentation.sourceSylowHom_endpoint Q split roots rels hU e hf,
    G2Presentation.sourceSylow_card_le Q split roots rels hU e hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
