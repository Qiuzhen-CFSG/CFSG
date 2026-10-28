module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryLowerExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCompleteConsumer

/-!
# The full marked octagon comparison at a linear source endpoint

The actual F.1.1 opposite-factor catalogue leaves the Ree data, a linear
factor, or a special/projective unitary factor. Fong--Seitz (6G) and the
linear/unitary branch of (6F) exclude the latter alternatives. The source
therefore supplies the complete (6H) data and its Section 10 comparison.

The resulting isomorphism concerns the original local amalgam and retains
the entire Borel and both inclusion squares. All positive linear degrees
are included, including the binary Ree parameter zero. No ambient-completion
identification or classification callback is used.

Source: Fong--Seitz I (6F)--(6H), pp.45--56; II, Section 10;
DGS, Groups and Graphs, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

open ReeSource

/-- The source catalogue selects actual (6H) data at every linear endpoint,
with no remaining linear or unitary alternative. -/
theorem original_linear_octagon_sixH (hm : rotationOrder Q=8)
    {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ m, Nonempty (OriginalReeSixHData Q e split n m) := by
  rcases original_octagon_source_selection Q e h split hm hn hi with
    hree | ⟨b,hb,hj,_⟩ | ⟨b,hb,hj,_⟩ | ⟨b,hb,hj,_⟩
  · exact hree
  · exact (original_linear_pair_false Q e h split hm 0 1 (by decide) hn hb hi hj).elim
  · exact (original_linear_unitary_pair_false Q e h split hm 0 1 (by decide) hn hb hi (Or.inl hj)).elim
  · exact (original_linear_unitary_pair_false Q e h split hm 0 1 (by decide) hn hb hi (Or.inr hj)).elim

/-- The source-selected octagon has the full original marked Ree amalgam,
including parameter zero and either orientation of the model. -/
theorem original_linear_octagon_comparison (hm : rotationOrder Q=8)
    {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ m, n=2*m+1 ∧
      (Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
          inf_le_left inf_le_right) (GreenBook.LieModels.ReeFour.amalgam m)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
          inf_le_left inf_le_right) (GreenBook.LieModels.ReeFour.amalgam m).reverse)) := by
  obtain ⟨m,⟨c⟩⟩ := original_linear_octagon_sixH Q e h split hm hn hi
  exact ⟨m,c.common_field,ReeSection10.concrete_comparison_ofSixHData Q split e c.toReeSixHData⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
