module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledOriginal

/-!
# Narrow original doubled source interface

The proof imports remain internal so that the actual doubled-row producer
can be combined with the independent Hermitian and structural source cones.
The public type retains exactly the original chosen module and hypotheses.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original marked non-FF doubled exclusion, with a narrow public import boundary. -/
theorem sourceOrbit_nonFF_doubled_excluded_original
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : False :=
  D.sourceOrbit_markedDoubled_nonFF_excluded_of_many h hmany hd hnon
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
