module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SixCoordinates
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Obstruction

/-!
# Construction of the original dimension-four source local data

The literal source reduction gives either the required local data or the
six-dimensional swapping action. Its rotating cubic is now excluded: the
exhaustive basis-image census and the representative words produce a
point-fixing element of order seven, contradicting the actual order bound
4608 for the source point stabilizer. This closes the remaining swapping
case with the full ambient selected-counterexample hypotheses retained.

The constructor proves the two core equalities, quotient order eighteen,
and the generation and inversion identities on the literal quotient. Its
application constructs the genuine I.4.5 configuration on the original
subgroups. Universal recognition remains with qt-i45-g2-recognition;
qt-d-14414-g2-source retains its final application, and qt-d-14414-source
retains discharge of the earlier-source inputs and the 14.4.14 assembly.

Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual enlarged swapping configuration is impossible. -/
theorem no_six_dimensional_swapping : ¬ SixDimensionalSwappingCase := by
  rintro ⟨J,q,hp,hq,hr,hb⟩
  exact BinarySixSplitPair.no_rotating_cubic J q hp hq hr hb

/-- The source local-data constructor, with no extra local, normalizer,
fusion, coordinate or recognition premise. Earlier source theorems retain
their independent producers and final discharge in qt-d-14414-source. -/
theorem source_localData
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (SourceLocalData L F) := by
  rcases source_localData_or_six_dimensional_swapping d earlier hq chosen previous F hne hZ hcard with
    hd | hs
  · exact hd
  · exact (no_six_dimensional_swapping hs).elim

/-- Literal application of the completed local constructor to the original
I.4.5 configuration; no local-data callback remains. -/
theorem source_configuration
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) := by
  obtain ⟨localData⟩ := source_localData d earlier hq chosen previous F hne hZ hcard
  exact configuration_of_source_local d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard localData

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
