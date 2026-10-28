module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticFourPresentation.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The C₂ presentation in the original Chapter12 selected-factor consumer

The existing preparation supplies genuine F.1.1 for the same selected pair
and its original S. Compatible eight-root data on its independently marked
finite quotient now produce the actual symplectic amalgam comparison used
by ConcreteAmalgamComparison. The field's two-power cardinality is derived
internally. No perfection of both endpoints or unknown quotient simplicity
is required. Exhaustive source row selection and construction of the root
data remain with the source recognition and final Chapter12 assembly owners.

Source: DGS Theorem D, printed p.224; Aschbacher–Smith 12.2.2, p.795,
and F.1.1–12, pp.259–264. This is the literal regular C₂ conditional branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {F : Type} [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal selected-factor consumer obtains an actual symplectic amalgam
comparison. Source reconstruction of the eight compatible roots remains explicit. -/
theorem rankOne_c2_presentation_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (roots : C2Presentation.RootData (F := F) Q split)
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
  obtain ⟨m,_,hm⟩ := FiniteField.card F 2
  exact Global.ConcreteAmalgamComparison.symplectic F m m.property
    (by simpa only [Nat.card_eq_fintype_card] using hm)
    (Or.inl ⟨SymplecticFourPresentation.comparison Q e hf split roots⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
