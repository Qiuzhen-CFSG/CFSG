module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuffix
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiOpposite
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiOppositeTable

/-!
# Source equations away from the opposite Suzuki pair

The suffix after `B₀` has its own ordered realization.  This module exposes
the exact finite premise needed by the opposite Suzuki calculation: every
ordered angular equation except the pair `(B₀,B₂)`.  It constructs the suffix
equations and the resulting realization, while retaining the missing pair as
an explicit boundary for the source owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The complete ordered angular family with only `(B₀,B₂)` removed. -/
def AngularEquationsExceptOpposite : Prop :=
  ∀ (i j : PositiveTables.Root),
    ¬ (i = .inr 0 ∧ j = .inr 2) →
    ∀ (hj : j ∈ tail sourceOrder i)
      (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j),
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b)

theorem angularSuffixEquations_of_except
    (H : AngularEquationsExceptOpposite Q split c) :
    Equations (AngularSuffix.table m) (synchronizedSourceRoot Q split c) := by
  apply AngularSuffix.equations m (synchronizedSourceRoot Q split c)
  intro i j hi hj a b
  apply H i j
  intro h
  exact hi h.1

def angularSuffixRealization
    (H : AngularEquationsExceptOpposite Q split c) :
    AngularSuffix.Carrier m →* X ⧸ Q.D :=
  AngularSuffix.realization m (synchronizedSourceRoot Q split c)
    (angularSuffixEquations_of_except Q split c H)

@[simp] theorem angularSuffixRealization_root
    (H : AngularEquationsExceptOpposite Q split c)
    (i : PositiveTables.Root) (hi : i ∈ AngularSuffix.suffixOrder)
    (a : AngularPresentation.Parameter m i) :
    angularSuffixRealization Q split c H (AngularSuffix.root m i hi a) =
      synchronizedSourceRoot Q split c i a :=
  AngularSuffix.realization_root m (synchronizedSourceRoot Q split c)
    (angularSuffixEquations_of_except Q split c H) i hi a

theorem angularSuffixRealization_firstAction_root
    (H : AngularEquationsExceptOpposite Q split c)
    (a : AngularPresentation.Parameter m (.inr 0))
    (i : PositiveTables.Root) (hi : i ∈ AngularSuffix.suffixOrder)
    (hopp : i ≠ .inr 2)
    (b : AngularPresentation.Parameter m i) :
    angularSuffixRealization Q split c H
        (AngularSuffix.firstAction m a (AngularSuffix.root m i hi b)) =
      synchronizedSourceRoot Q split c (.inr 0) a *
        synchronizedSourceRoot Q split c i b *
        (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ := by
  have hj : i ∈ tail sourceOrder (.inr 0) := hi
  have htab := AngularPresentation.native_equations m (.inr 0) i hj a b
  have hfa : AngularSuffix.firstAction m a (AngularSuffix.root m i hi b) =
      ⟨word (AngularPresentation.Parameter m) (fun k => AngularPresentation.nativeRoot m k)
          AngularSuffix.suffixOrder
          ((AngularPresentation.table m).conjugate (.inr 0) i hj a b),
        word_mem_join _ _ _ _⟩ := by
    apply Subtype.ext
    change (a : Model m) * (b : Model m) * (a : Model m)⁻¹ = _
    exact htab
  rw [hfa]
  change AngularSuffix.realization m (synchronizedSourceRoot Q split c)
      (angularSuffixEquations_of_except Q split c H) _ = _
  rw [AngularSuffix.realization_word]
  change word (AngularPresentation.Parameter m)
      (fun k => synchronizedSourceRoot Q split c k)
      (tail sourceOrder (.inr 0))
      ((AngularPresentation.table m).conjugate (.inr 0) i hj a b) = _
  exact (H (.inr 0) i (by
    intro h
    exact hopp h.2) hj a b).symm

theorem synchronized_suzukiOpposite_pure_ordered_equation
    (_H : AngularEquationsExceptOpposite Q split c)
    (hpure : ∀ (a y : CoefficientField m),
      synchronizedSourceRoot Q split c (.inr 0)
          (PositiveTables.rootChartEquiv m (.inr 0) (a,0)) *
        synchronizedSourceRoot Q split c (.inr 2)
          (PositiveTables.rootChartEquiv m (.inr 2) (y,0)) *
        (synchronizedSourceRoot Q split c (.inr 0)
          (PositiveTables.rootChartEquiv m (.inr 0) (a,0)))⁻¹ =
      word (AngularPresentation.Parameter m)
        (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 0))
        (AngularSuzukiOppositeTable.tail06 m a 0 y 0)) :
    ∀ (a y : CoefficientField m),
      synchronizedSourceRoot Q split c (.inr 0)
          (PositiveTables.rootChartEquiv m (.inr 0) (a,0)) *
        synchronizedSourceRoot Q split c (.inr 2)
          (PositiveTables.rootChartEquiv m (.inr 2) (y,0)) *
        (synchronizedSourceRoot Q split c (.inr 0)
          (PositiveTables.rootChartEquiv m (.inr 0) (a,0)))⁻¹ =
      word (AngularPresentation.Parameter m)
        (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 0))
        ((AngularPresentation.table m).conjugate (.inr 0) (.inr 2)
          (by
            change (.inr 2 : PositiveTables.Root) ∈
              ([.inl 1, .inr 3, .inl 3, .inr 1, .inl 2, .inr 2, .inl 0] :
                List PositiveTables.Root)
            simp)
          (PositiveTables.rootChartEquiv m (.inr 0) (a,0))
          (PositiveTables.rootChartEquiv m (.inr 2) (y,0))) := by
  intro a y
  rw [AngularSuzukiOppositeTable.table06, hpure]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
