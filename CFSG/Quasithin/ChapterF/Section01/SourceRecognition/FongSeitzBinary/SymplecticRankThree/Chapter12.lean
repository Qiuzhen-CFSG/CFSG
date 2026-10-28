module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Comparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Literal Chapter12 comparison after normal symplectic recognition

The original selected-factor preparation supplies F.1.1. The actual two
root orders and m=4 give the source Sylow order. A normal Sp₄ subgroup of
that order is the whole finite marked quotient, and the full marked
comparison supplies the symplectic alternative, in either orientation.
The field cardinality is a positive power of two, including two itself.

The normal symplectic subgroup and its equivalence are explicit premises,
still to be constructed by the rank-three geometric proof. This adapter
does not complete the original source recognition or exhaustive catalogue.
Source: Fong–Seitz II (7C), p.193; DGS Theorem D, p.224;
Aschbacher–Smith 12.2.2, p.795, and F.1.1–12, pp.259–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {F : Type} [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original comparison consumer, conditional only on the explicitly
unproved normal symplectic recognition and the genuine earlier row inputs. -/
theorem rankOne_c2_rankThree_comparison_of_normal_symplectic
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = Nat.card F)
    (hq1 : Nat.card (simpleRoot Q split 1) = Nat.card F)
    (hgen : split.unipotentClosure = ⊤)
    (K : Subgroup (X ⧸ Q.D)) [K.Normal] (model : K ≃* Sp F)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  let := Fintype.ofFinite F
  obtain ⟨m,_,hF⟩ := FiniteField.card F 2
  exact Global.ConcreteAmalgamComparison.symplectic F m m.property
    (by simpa only [Nat.card_eq_fintype_card] using hF)
    (SymplecticRankThree.comparison_of_normal_symplectic Q e hf split hm hq0 hq1 hgen K model)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
