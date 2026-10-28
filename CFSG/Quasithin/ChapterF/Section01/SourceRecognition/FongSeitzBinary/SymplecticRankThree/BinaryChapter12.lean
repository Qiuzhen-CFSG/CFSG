module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.BinaryComparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The binary C₂ source comparison in the literal Chapter12 consumer

The original preparation supplies F.1.1 and hence local characteristic two
on the same marked quotient. The selected m=4 row with roots of order two
is recognized as full Sp₄(F₂), and the full Borel and both endpoint markings
give the symplectic alternative of `ConcreteAmalgamComparison`. Both
orientations and the supplied quotient map are retained. This binary
application assumes no model homomorphism or geometric recognition theorem.
The other field sizes remain with the general source-recognition family.

Source: Fong–Seitz II (7C), p.193, and (8A), p.197;
Aschbacher–Smith 12.2.2 and F.1.1–12.
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

  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal Chapter12 symplectic alternative from the original binary row. -/
theorem rankOne_c2_binary_rankThree_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = 2)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
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
  exact Global.ConcreteAmalgamComparison.symplectic (ZMod 2) 1 (by decide)
    (by norm_num [Nat.card_eq_fintype_card])
    (SymplecticRankThree.binary_comparison Q e hf split hm hq hrow)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
