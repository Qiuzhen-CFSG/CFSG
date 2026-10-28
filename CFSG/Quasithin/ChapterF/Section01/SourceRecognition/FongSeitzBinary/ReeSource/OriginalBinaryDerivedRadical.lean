module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryDerivedRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Original-endpoint application of the binary derived-radical module

The source binary module is transported through the already established
original endpoint equivalence.  This keeps the actual original two-core and
the literal marked quotient in the consumer; no derived-model replacement is
made.  The order-five movement witness remains visible because it is the
remaining binary (6H) source case analysis.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include e hB in
theorem original_binary_derivedRadical_frattini_card_ge
    (c : rankOne Q split i) (hc : orderOf c = 5)
    (hmove : (derivedRadicalSection Q split i hV).action c ≠ 1) :
    2^4 ≤ Nat.card
      (commutator (pCore 2 (parabolic L S i)) ⧸
        frattini (commutator (pCore 2 (parabolic L S i)))) := by
  rw [Nat.card_congr (originalDerivedFrattiniEquiv Q e split i hV).toEquiv]
  exact binary_derivedRadical_frattini_card_ge Q split i hV μ hB c hc hmove

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
