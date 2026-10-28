module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NextConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAdjacent

/-!
# Section 10 construction after the adjacent and next-linear families

Seven adjacent equations, the five original computed equations and the two
next-linear reflection transforms supply fourteen literal ordered pairs.
The remaining fourteen equations are kept explicit, including the nontrivial
linear and Suzuki mixed coefficients. The actual original octagon consumer
retains both endpoint and whole-Borel markings and assumes no odd degree.

Source: Fong--Seitz II, Section 10; Fong--Seitz I (1J), (6H).
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

/-- The fourteen outstanding whole-root pairs after both checked families. -/
def RemainingAfterAdjacentEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

/-- Discharge the adjacent cases in the previous exact construction interface. -/
theorem remainingAfterNextEquations_of_adjacent {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterAdjacentEquations Q split c) :
    RemainingAfterNextEquations Q split c := by
  intro i j hc hn hj a b
  by_cases ha : AdjacentAngularPair i j
  · exact synchronized_adjacentAngular_equation Q split c i j ha hj a b
  · exact E i j hc hn ha hj a b

/-- Construct the full marked data from the fourteen remaining equations. -/
def Section10Construction.ofAdjacentAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterAdjacentEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofNextAngular Q split c
    (remainingAfterNextEquations_of_adjacent Q split c E)

/-- Apply all fourteen proved pairs to the actual original marked octagon. -/
def Section10Construction.ofOriginalOctagonAdjacent
    (E : RemainingAfterAdjacentEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonNext Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterNextEquations_of_adjacent Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
