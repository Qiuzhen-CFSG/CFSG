module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.EndpointKnownRows
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuffix

/-!
# Unconditional realization of the seven-root source suffix

The checked angular families already cover every pair internal to the suffix
following the first Suzuki root. They therefore construct a homomorphism from
that native suffix into the marked source quotient, independently of the two
first-root end equations. This transports all interior collections used in the
last two source calculations.

Source: Fong--Seitz II, Section 10, positive-root collection before (10.23)--(10.41).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- All internal suffix equations are already proved from the source. -/
theorem angularSuffixEquations :
    Equations (AngularSuffix.table m) (synchronizedSourceRoot Q split c) := by
  apply AngularSuffix.equations
  intro i j hi hj a b
  apply synchronizedAngularEquation_of_not_suzukiEnd Q split c i j _ hj a b
  rintro (⟨h,_⟩ | ⟨h,_⟩)
  · exact hi h
  · exact hi h

/-- The native suffix evaluates into the source without either end equation. -/
def angularSuffixEval : AngularSuffix.Carrier m →* X ⧸ Q.D :=
  AngularSuffix.realization m (synchronizedSourceRoot Q split c)
    (angularSuffixEquations Q split c)

@[simp] theorem angularSuffixEval_root (i : PositiveTables.Root)
    (hi : i ∈ AngularSuffix.suffixOrder) (a : AngularPresentation.Parameter m i) :
    angularSuffixEval Q split c (AngularSuffix.root m i hi a) =
      synchronizedSourceRoot Q split c i a :=
  AngularSuffix.realization_root m (synchronizedSourceRoot Q split c)
    (angularSuffixEquations Q split c) i hi a

/-- Every native ordered suffix word transports literally into the source. -/
theorem angularSuffixEval_word (p : Tuple (AngularPresentation.Parameter m) AngularSuffix.suffixOrder) :
    angularSuffixEval Q split c
      ⟨word (AngularPresentation.Parameter m) (fun i => AngularPresentation.nativeRoot m i)
        AngularSuffix.suffixOrder p, word_mem_join _ _ _ _⟩ =
      word (AngularPresentation.Parameter m) (fun i => synchronizedSourceRoot Q split c i)
        AngularSuffix.suffixOrder p :=
  AngularSuffix.realization_word m (synchronizedSourceRoot Q split c)
    (angularSuffixEquations Q split c) p

/-- The five already-known first-root actions intertwine on whole suffix roots. -/
theorem angularSuffixEval_firstAction_root
    (a : AngularPresentation.Parameter m (.inr 0))
    (i : PositiveTables.Root) (hi : i ∈ AngularSuffix.suffixOrder)
    (hopp : i ≠ .inr 2) (hlast : i ≠ .inl 0)
    (b : AngularPresentation.Parameter m i) :
    angularSuffixEval Q split c
      (AngularSuffix.firstAction m a (AngularSuffix.root m i hi b)) =
      synchronizedSourceRoot Q split c (.inr 0) a *
        synchronizedSourceRoot Q split c i b *
        (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ := by
  have hj : i ∈ tail sourceOrder (.inr 0) := hi
  have hfa : AngularSuffix.firstAction m a (AngularSuffix.root m i hi b) =
      ⟨word (AngularPresentation.Parameter m) (fun k => AngularPresentation.nativeRoot m k)
          AngularSuffix.suffixOrder
          ((AngularPresentation.table m).conjugate (.inr 0) i hj a b),
        word_mem_join _ _ _ _⟩ := by
    apply Subtype.ext
    change (a : Model m) * (b : Model m) * (a : Model m)⁻¹ = _
    exact AngularPresentation.native_equations m (.inr 0) i hj a b
  rw [hfa,angularSuffixEval_word]
  exact (synchronizedAngularEquation_of_not_suzukiEnd Q split c (.inr 0) i (by
    rintro (⟨_,h⟩ | ⟨_,h⟩)
    · exact hopp h
    · exact hlast h) hj a b).symm
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
