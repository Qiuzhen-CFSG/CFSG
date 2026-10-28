module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourcePlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Whole source projective planes in the Chapter12 preparation

The original preparation supplies F.1.1 on the same marked quotient.
Completing the constructed affine coordinates and projecting between blocks
now identifies every actual closed neighbor block with PG(2,F), preserving
its literal orbital lines, including q=2 and q=4. No coordinate input is
required. The compatible extension of these plane coordinates to PG(3,F)
and the final nonbinary symplectic comparison remain with this source owner.

Source: Higman (1964), Lemma 10 and Theorem 2(i); Fong–Seitz II (7C), (8A);
Aschbacher–Smith 12.2.2 and F.1.1–12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
open Theory.GroupAction.SymplecticRankThree
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {F : Type} [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
include D

/-- Projective-plane coordinates on every original orbital block, from
the literal Chapter12 preparation and selected source row. -/
theorem rankOne_c2_projective_planes_of_linear_row
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∀ p : C2RankThree.Points Q 1,
      ∃ C : ↥(SymplecticRankThree.orbitalBlock Q p) ≃ Projectivization F (F × (F × F)),
        ∀ a b x : ↥(SymplecticRankThree.orbitalBlock Q p),
          (C x).submodule ≤ (C a).submodule ⊔ (C b).submodule ↔
            (x : C2RankThree.Points Q 1) ∈ SymplecticRankThree.orbitalLine Q a b := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact SymplecticRankThree.marked_projective_planes_of_linear_row Q e hf split hm μ hq hrow

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
