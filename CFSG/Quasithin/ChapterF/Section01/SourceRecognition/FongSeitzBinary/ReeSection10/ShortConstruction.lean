module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AdjacentConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularShortCompletion

/-!
# Construction after completion of the short mixed angular family

The terminal short relation at positions (4,7) removes one further literal
case from the adjacent-family construction boundary. The original marked
consumer retains all source hypotheses and uses the already discharged odd
linear degree. The remaining thirteen angular cases are still explicit.

Source: Fong--Seitz II, Section 10, (10.11)(i) and its Weyl transforms.
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


/-- The thirteen cases remaining after all five short mixed equations. -/
def RemainingAfterShortEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ¬ (i = .inr 1 ∧ j = .inl 0) →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Discharge the last short case at the existing fourteen-case boundary. -/
theorem remainingAfterAdjacentEquations_of_short {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterShortEquations Q split c) :
    RemainingAfterAdjacentEquations Q split c := by
  intro i j hc hn ha hj a b
  by_cases hs : i = .inr 1 ∧ j = .inl 0
  · rcases hs with ⟨rfl,rfl⟩
    exact synchronized_terminalAngular_equation Q split c hj a b
  · exact E i j hc hn ha hs hj a b

/-- Construct the full marked data from the thirteen remaining equations. -/
def Section10Construction.ofShortAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterShortEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofAdjacentAngular Q split c
    (remainingAfterAdjacentEquations_of_short Q split c E)

/-- Apply the completed short family to the literal original marked octagon. -/
def Section10Construction.ofOriginalOctagonShort
    (E : RemainingAfterShortEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonAdjacent Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterAdjacentEquations_of_short Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
