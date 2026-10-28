module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.ShortConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLinearCommute

/-!
# Section 10 construction after the commuting linear family

Five literal linear angular equations remove five cases from the original
marked-octagon constructor. Eight noncommuting cases remain explicit; all
original source hypotheses and synchronized field parameters are preserved.

Source: Fong--Seitz II, Section 10, (10.2)(iv), (10.3), and Weyl transport.
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


open ReeF4.RootPresentationRecognition
open ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation


/-- The eight cases remaining after the five commuting linear pairs. -/
def RemainingAfterLinearEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ¬ (i = .inr 1 ∧ j = .inl 0) →
    ¬ LinearCommutingAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Apply the five newly proved equations to the thirteen-case boundary. -/
theorem remainingAfterShortEquations_of_linear {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterLinearEquations Q split c) :
    RemainingAfterShortEquations Q split c := by
  intro i j hc hn ha hs hj a b
  by_cases hl : LinearCommutingAngularPair i j
  · exact synchronized_linearAngular_equation Q split c i j hl hj a b
  · exact E i j hc hn ha hs hl hj a b

/-- Construct the full marked data from the eight remaining equations. -/
def Section10Construction.ofLinearAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterLinearEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofShortAngular Q split c
    (remainingAfterShortEquations_of_linear Q split c E)

/-- Apply the commuting linear family to the literal original marked octagon. -/
def Section10Construction.ofOriginalOctagonLinear
    (E : RemainingAfterLinearEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonShort Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterShortEquations_of_linear Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
