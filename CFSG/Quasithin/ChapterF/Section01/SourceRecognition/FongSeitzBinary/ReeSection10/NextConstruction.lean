module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalAngular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularNextTransforms

/-!
# Construction after the next-linear reflection family

The two new nonadjacent equations discharge their cases at the existing
construction boundary. The original marked consumer retains the full Borel
markings and uses the octagon theorem to discharge odd linear degree.
Adjacent equations remain available for separate assembly; this module does
not claim that the remaining 21 pairs have been proved.

Source: Fong--Seitz II, Section 10, with Fong--Seitz I (1J), (6H).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ ReeSource.originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))


/-- Full construction from the remaining 21 cases on any marked Section 10 input. -/
def Section10Construction.ofNextAngular {n m : ℕ}
    (c : ReeSixHData Q split n m)
    (E : RemainingAfterNextEquations Q split c) : Section10Construction Q split n m :=
  Section10Construction.ofRemainingAngular Q split c (remainingAngularEquations_of_next Q split c E)

/-- The same reduction on the actual original octagon; no odd-degree premise. -/
def Section10Construction.ofOriginalOctagonNext
    (E : RemainingAfterNextEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagon Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAngularEquations_of_next Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
