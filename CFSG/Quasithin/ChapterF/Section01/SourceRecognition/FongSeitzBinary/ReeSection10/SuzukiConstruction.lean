module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.ShortConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuzukiCommute
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuzukiNear

/-!
# Section 10 after the perpendicular and nearby Suzuki families

The two perpendicular commutations and three nearby Suzuki equations remove
five literal angular pairs from the completed short-family interface. The
remaining eight cases consist of five commuting linear pairs and the three
mixed end cases. The original octagon consumer retains all original markings.

Source: Fong--Seitz II, (10.2)(iv), (10.8), and their Weyl transforms.
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



/-- The eight cases outside the proved short, adjacent and Suzuki families. -/
def RemainingAfterSuzukiEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ¬ (i = .inr 1 ∧ j = .inl 0) →
    ¬ SuzukiCommuteAngularPair i j → ¬ NearSuzukiAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Discharge the five Suzuki cases in the completed short-family interface. -/
theorem remainingAfterShortEquations_of_suzuki {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterSuzukiEquations Q split c) :
    RemainingAfterShortEquations Q split c := by
  intro i j hc hn ha hs hj a b
  by_cases hp : SuzukiCommuteAngularPair i j
  · exact synchronized_suzukiCommuteAngular_equation Q split c i j hp hj a b
  by_cases hq : NearSuzukiAngularPair i j
  · exact synchronized_nearSuzukiAngular_equation Q split c i j hq hj a b
  exact E i j hc hn ha hs hp hq hj a b

/-- Construct the full marked data from the eight remaining equations. -/
def Section10Construction.ofSuzukiAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterSuzukiEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofShortAngular Q split c
    (remainingAfterShortEquations_of_suzuki Q split c E)

/-- Apply all five Suzuki equations to the literal original marked octagon. -/
def Section10Construction.ofOriginalOctagonSuzuki
    (E : RemainingAfterSuzukiEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonShort Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterShortEquations_of_suzuki Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
