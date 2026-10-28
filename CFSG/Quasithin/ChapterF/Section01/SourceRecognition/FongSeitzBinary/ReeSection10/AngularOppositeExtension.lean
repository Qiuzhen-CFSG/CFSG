module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSix
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularEndExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeMain

/-!
# The whole opposite Suzuki angular equation

The source realization of the six interior root groups intertwines the first
Suzuki root action. On five of its main curves this is an earlier angular row;
on the opposite Suzuki curve it is the proved pure opposite commutator.
Generation extends these checks to the entire six-root carrier and actor root,
so the whole opposite angular row is independent of the final linear-root row.

Source: Fong--Seitz II, Section 10, (10.23)--(10.41).
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

def angularSixEval : AngularSix.Carrier m →* X ⧸ Q.D :=
  (angularSuffixEval Q split c).comp (AngularSix.inclusion m)

@[simp] theorem angularSixEval_root (i : PositiveTables.Root) (hi : i ∈ AngularSix.order)
    (a : AngularPresentation.Parameter m i) :
    angularSixEval Q split c (AngularSix.root m i hi a) = synchronizedSourceRoot Q split c i a := by
  change angularSuffixEval Q split c (AngularSix.inclusion m (AngularSix.root m i hi a)) = _
  rw [AngularSix.inclusion_root,angularSuffixEval_root]

theorem angularSixEval_firstAction (hopp : SuzukiOppositePureEquation Q split c)
    (a : AngularPresentation.Parameter m (.inr 0)) (v : AngularSix.Carrier m) :
    angularSixEval Q split c (AngularSix.firstAction m a v) =
      synchronizedSourceRoot Q split c (.inr 0) a * angularSixEval Q split c v *
        (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ := by
  apply AngularSix.firstAction_intertwining m
    (synchronizedSourceRoot Q split c (.inr 0)) (angularSixEval Q split c) _ a v
  intro t i hi y
  simp only [angularSixEval,MonoidHom.comp_apply,AngularSix.inclusion_firstAction,AngularSix.inclusion_root]
  by_cases he : i = .inr 2
  · subst i
    simp only [AngularSuffix.mainParameter,angularSuffixEval_root,
      map_inv (synchronizedSourceRoot Q split c (.inr 0)),inv_inv]
    rw [synchronizedSourceRoot_field Q split c (.inr 0) (t,0),
      synchronizedSourceRoot_field Q split c (.inr 2) (y,0)]
    exact angularSuffixEval_oppositeMain_action Q split c hopp t y
  have hl : i ≠ .inl 0 := by
    intro he
    subst i
    have hb := (AngularSix.member _).mp hi
    simpa [rootIndex,Sum.elim,ReeF4.NormalizedRootCentralizers.CenterExponent.positive_pair_indices] using hb.2
  simpa only [angularSuffixEval_root] using
    angularSuffixEval_firstAction_root Q split c (AngularSuffix.mainParameter m (.inr 0) t)⁻¹
      i (AngularSix.member_suffix i hi) he hl (AngularSuffix.mainParameter m i y)

/-- Pure opposite commutators suffice for the whole opposite row, without the last row. -/
theorem synchronized_suzukiOppositeAngular_equation_of_pure
    (hopp : SuzukiOppositePureEquation Q split c)
    (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a : AngularPresentation.Parameter m (.inr 0)) (b : AngularPresentation.Parameter m (.inr 2)) :
    synchronizedSourceRoot Q split c (.inr 0) a * synchronizedSourceRoot Q split c (.inr 2) b *
      (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 0)) ((AngularPresentation.table m).conjugate (.inr 0) (.inr 2) hj a b) := by
  have hi : (.inr 2 : PositiveTables.Root) ∈ AngularSix.order := by simp [AngularSix.order]
  have he := angularSixEval_firstAction Q split c hopp a (AngularSix.root m (.inr 2) hi b)
  simp only [angularSixEval,MonoidHom.comp_apply,AngularSix.inclusion_firstAction,
    AngularSix.inclusion_root,angularSuffixEval_root] at he
  have hfa : AngularSuffix.firstAction m a
      (AngularSuffix.root m (.inr 2) (AngularSix.member_suffix _ hi) b) =
      ⟨word (AngularPresentation.Parameter m) (fun k => AngularPresentation.nativeRoot m k)
          AngularSuffix.suffixOrder ((AngularPresentation.table m).conjugate (.inr 0) (.inr 2) hj a b),
        word_mem_join _ _ _ _⟩ := by
    apply Subtype.ext
    change (a : Model m) * (b : Model m) * (a : Model m)⁻¹ = _
    exact AngularPresentation.native_equations m (.inr 0) (.inr 2) hj a b
  rw [hfa,angularSuffixEval_word] at he
  exact he.symm

/-- The source's proved pure identity closes the full opposite Suzuki angular row. -/
theorem synchronized_suzukiOppositeAngular_equation
    (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a : AngularPresentation.Parameter m (.inr 0)) (b : AngularPresentation.Parameter m (.inr 2)) :
    synchronizedSourceRoot Q split c (.inr 0) a * synchronizedSourceRoot Q split c (.inr 2) b *
      (synchronizedSourceRoot Q split c (.inr 0) a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder (.inr 0)) ((AngularPresentation.table m).conjugate (.inr 0) (.inr 2) hj a b) :=
  synchronized_suzukiOppositeAngular_equation_of_pure Q split c
    (synchronized_opposite_main_commutator Q split c) hj a b
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

