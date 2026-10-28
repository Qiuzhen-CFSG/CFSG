module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionBlocks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionTriality

/-!
# Actual block-amalgam comparisons in the Chapter12 generic branch

An isomorphism with either orientation of the linear-three or symplectic-four
amalgam identifies both original local factors as natural blocks at the original
field exponent. In particular the binary models are impossible. Applying this
to the source-selected nonshort factor excludes all four compatible comparisons.
The alternative selecting the whole residual remains available, including the
special U₅(4) row. The source overlap still contains both odd Cartans.

The independent uniqueness and F.1.12 core-bound premises remain explicit.
Exhaustive amalgam classification and ambient completion remain with
qt-d-1222-rankone-generic-global, with final source discharge retained by
qt-d-1222-rankone-generic and qt-d-1361-source.
Source: Aschbacher–Smith 5.2.6–7, pp.650–651, and the application on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both actual linear amalgam orientations recover the original exponent
and the complete natural-block structures of the same L and R. -/
theorem rankOne_global_linear_blocks
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) (LinearThree.amalgam F).reverse)) :
    m = n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n :=
  d.linear_amalgam_blocks (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F hm hF he

/-- The same original-field identification for both symplectic orientations. -/
theorem rankOne_global_symplectic_blocks
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) (SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) (SymplecticFour.amalgam F).reverse)) :
    m = n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n :=
  d.symplectic_amalgam_blocks (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F hm hF he

/-- The original core-bound selection leaves the whole residual or a factor
excluding all four concrete block amalgams, including their binary cases. -/
theorem rankOne_global_residual_or_block_exclusions_of_core_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R ∧
      (R = residual H ∨ ¬ ChapterC.IsShort R ∧
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (m : ℕ),
          0 < m → Nat.card F = 2^m →
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          ¬ Nonempty (RankTwoAmalgam.Iso α (LinearThree.amalgam F)) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (LinearThree.amalgam F).reverse) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (SymplecticFour.amalgam F)) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (SymplecticFour.amalgam F).reverse)) := by
  obtain ⟨A,B,R,d,hp,hr⟩ := D.rankOne_global_residual_or_not_short_of_core_bound
    h hmany hn hpsl hH hpar hthree hN hunique hcore
  refine ⟨A,B,R,d,hp,?_⟩
  rcases hr with he | hnot
  · exact Or.inl he
  · refine Or.inr ⟨hnot,?_⟩
    intro F _ _ _ m hm hF
    exact d.not_block_amalgams (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH.1.1.2 hp hnot F hm hF

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
