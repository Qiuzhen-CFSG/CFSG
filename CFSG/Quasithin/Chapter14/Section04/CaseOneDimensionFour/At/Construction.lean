module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Construction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.SixCoordinates

/-!
# Construction of the original dimension-four source local data at the original G,T

The literal source reduction gives either the required local data or the
six-dimensional swapping action. Its rotating cubic is now excluded: the
exhaustive basis-image census and the representative words produce a
point-fixing element of order seven, contradicting the actual order bound
4608 for the source point stabilizer. This closes the remaining swapping
case with the full ambient selected-counterexample hypotheses retained.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The local source-data constructor, with no additional local, normalizer,
fusion, coordinate or recognition premise. Earlier source inputs retain
their producers and final discharge in the 14.4.14 assembly. -/
theorem source_localData
    (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (SourceLocalData L F) := by
  rcases source_localData_or_six_dimensional_swapping d setup structural alternatives F hne hZ hcard with
    hd | hs
  · exact hd
  · exact (no_six_dimensional_swapping hs).elim

/-- The configuration retains the original point normalizer and natural block. -/
theorem source_configuration_on
    (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ c : DimensionFour.G2ThreeConfiguration G, c.H = F.H ∧ c.M = L := by
  obtain ⟨localData⟩ := source_localData d setup structural alternatives F hne hZ hcard
  exact configuration_on_of_source_local d setup structural alternatives F hne hZ hcard localData

/-- Literal application of the completed local constructor to the original
I.4.5 configuration; no local-data callback remains. -/
theorem source_configuration
    (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) := by
  obtain ⟨localData⟩ := source_localData d setup structural alternatives F hne hZ hcard
  exact configuration_of_source_local d setup structural
    alternatives F hne hZ hcard localData

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
