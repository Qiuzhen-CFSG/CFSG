module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FinalConstruction

/-!
# The established angular equations away from the two Suzuki ends

The eight proved angular families exhaust every ordered root pair except
`(0,6)` and `(0,7)`. This pointwise dispatcher supplies the internal seven-root
suffix equations before either missing endpoint relation is assumed.

Source: Fong--Seitz II (1974), Section 10, the established relations through
(10.26) and the mixed linear relation, in native triangular coordinates.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- Every angular pair outside the two endpoint rows is already determined. -/
theorem synchronizedAngularEquation_of_not_suzukiEnd (i j : PositiveTables.Root)
    (hend : ¬ SuzukiEndAngularPair i j) (hj : j ∈ tail sourceOrder i)
    (a : AngularPresentation.Parameter m i) (b : AngularPresentation.Parameter m j) :
    synchronizedSourceRoot Q split c i a * synchronizedSourceRoot Q split c j b *
      (synchronizedSourceRoot Q split c i a)⁻¹ =
      word (AngularPresentation.Parameter m) (fun k => synchronizedSourceRoot Q split c k)
        (tail sourceOrder i) ((AngularPresentation.table m).conjugate i j hj a b) := by
  by_cases hc : ComputedAngularPair i j
  · exact synchronized_computedAngular_equation Q split c i j hc hj a b
  by_cases hn : NextAngularPair i j
  · exact synchronized_nextAngular_equation Q split c i j hn hj a b
  by_cases ha : AdjacentAngularPair i j
  · exact synchronized_adjacentAngular_equation Q split c i j ha hj a b
  by_cases hs : i = .inr 1 ∧ j = .inl 0
  · rcases hs with ⟨rfl,rfl⟩
    exact synchronized_terminalAngular_equation Q split c hj a b
  by_cases hl : LinearCommutingAngularPair i j
  · exact synchronized_linearAngular_equation Q split c i j hl hj a b
  by_cases hp : SuzukiCommuteAngularPair i j
  · exact synchronized_suzukiCommuteAngular_equation Q split c i j hp hj a b
  by_cases hq : NearSuzukiAngularPair i j
  · exact synchronized_nearSuzukiAngular_equation Q split c i j hq hj a b
  by_cases hm : i = .inl 1 ∧ j = .inl 0
  · rcases hm with ⟨rfl,rfl⟩
    exact synchronized_lastLinearAngular_equation Q split c hj a b
  exfalso
  fin_cases i <;> fin_cases j <;>
    simp_all [SuzukiEndAngularPair,ComputedAngularPair,NextAngularPair,
      AdjacentAngularPair,LinearCommutingAngularPair,SuzukiCommuteAngularPair,
      NearSuzukiAngularPair,rootIndex,sourceOrder,sourceIndex,tail,
      ReeF4.NormalizedRootCentralizers.CenterExponent.positive_pair_indices,
      ReeF4.NormalizedRootCentralizers.CenterExponent.positive_quartet_indices]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
