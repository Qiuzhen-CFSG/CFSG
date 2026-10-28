module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.MixedLinearSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastLinear

/-!
# Final Section 10 angular assembly boundary

The commuting linear family, the five Suzuki families and the mixed linear
equation compose to leave only `(0,6)` and `(0,7)` explicit in
`RemainingSuzukiEndEquations`. The preceding three-pair interface and its
constructors remain available.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open MarkedLocal ReeSource
open ReeF4.RootPresentationRecognition
open ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation

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

/- The residual noncommuting mixed cases after the checked families. -/
def RemainingAfterFinalEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ¬ (i = .inr 1 ∧ j = .inl 0) →
    ¬ LinearCommutingAngularPair i j → ¬ SuzukiCommuteAngularPair i j →
    ¬ NearSuzukiAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

theorem remainingAfterLinearEquations_of_final {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterFinalEquations Q split c) :
    RemainingAfterLinearEquations Q split c := by
  intro i j hc hn ha hs hl hj a b
  by_cases hp : SuzukiCommuteAngularPair i j
  · exact synchronized_suzukiCommuteAngular_equation Q split c i j hp hj a b
  by_cases hq : NearSuzukiAngularPair i j
  · exact synchronized_nearSuzukiAngular_equation Q split c i j hq hj a b
  exact E i j hc hn ha hs hl hp hq hj a b

def Section10Construction.ofFinalAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingAfterFinalEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofLinearAngular Q split c
    (remainingAfterLinearEquations_of_final Q split c E)

def Section10Construction.ofOriginalOctagonFinal
    (E : RemainingAfterFinalEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonLinear Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterLinearEquations_of_final Q split _ E)

/-- The two remaining angular positions, (0,6) and (0,7). -/
def SuzukiEndAngularPair (i j : PositiveTables.Root) : Prop :=
  (i = .inr 0 ∧ j = .inr 2) ∨ (i = .inr 0 ∧ j = .inl 0)

instance (i j : PositiveTables.Root) : Decidable (SuzukiEndAngularPair i j) := by
  unfold SuzukiEndAngularPair
  infer_instance

/-- Only the two Suzuki end equations remain after the mixed linear calculation. -/
def RemainingSuzukiEndEquations {n m : ℕ} (c : ReeSixHData Q split n m) : Prop :=
  ∀ (i j : PositiveTables.Root), SuzukiEndAngularPair i j →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

private theorem remaining_pair_cases : ∀ (i j : PositiveTables.Root),
    ¬ ComputedAngularPair i j → ¬ NextAngularPair i j →
    ¬ AdjacentAngularPair i j → ¬ (i = .inr 1 ∧ j = .inl 0) →
    ¬ LinearCommutingAngularPair i j → ¬ SuzukiCommuteAngularPair i j →
    ¬ NearSuzukiAngularPair i j → ¬ (i = .inl 1 ∧ j = .inl 0) →
    j ∈ tail sourceOrder i → SuzukiEndAngularPair i j := by
  intro i j hc hn ha hs hl hp hq hm
  fin_cases i <;> fin_cases j <;>
    simp_all [SuzukiEndAngularPair, ComputedAngularPair, NextAngularPair,
      AdjacentAngularPair, LinearCommutingAngularPair, SuzukiCommuteAngularPair,
      NearSuzukiAngularPair, rootIndex, sourceOrder, sourceIndex, tail,
      ReeF4.NormalizedRootCentralizers.CenterExponent.positive_pair_indices,
      ReeF4.NormalizedRootCentralizers.CenterExponent.positive_quartet_indices]

/-- Apply the proved (1,7) equation at the preceding three-pair boundary. -/
theorem remainingAfterFinalEquations_of_suzukiEnd {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingSuzukiEndEquations Q split c) :
    RemainingAfterFinalEquations Q split c := by
  intro i j hc hn ha hs hl hp hq hj a b
  by_cases hmixed : i = .inl 1 ∧ j = .inl 0
  · rcases hmixed with ⟨rfl,rfl⟩
    exact synchronized_lastLinearAngular_equation Q split c hj a b
  rcases remaining_pair_cases i j hc hn ha hs hl hp hq hmixed hj with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact E _ _ (Or.inl ⟨rfl,rfl⟩) hj a b
  · exact E _ _ (Or.inr ⟨rfl,rfl⟩) hj a b

/-- Construct the full marked data from just the two Suzuki end equations. -/
def Section10Construction.ofSuzukiEndAngular {n m : ℕ}
    (c : ReeSixHData Q split n m) (E : RemainingSuzukiEndEquations Q split c) :
    Section10Construction Q split n m :=
  Section10Construction.ofFinalAngular Q split c
    (remainingAfterFinalEquations_of_suzukiEnd Q split c E)

/-- The two-pair boundary on the literal original marked octagon. -/
def Section10Construction.ofOriginalOctagonSuzukiEnd
    (E : RemainingSuzukiEndEquations Q split
      (originalOctagonInput Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁)) :
    Section10Construction Q split n m :=
  Section10Construction.ofOriginalOctagonFinal Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    (remainingAfterFinalEquations_of_suzukiEnd Q split _ E)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
