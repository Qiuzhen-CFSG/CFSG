module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneInitialBounds
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!
# Initial Suzuki orbit bounds with the Held cover premise discharged

The finite quasisimple Held odd-center theorem supplies the remaining
input to the existing E.6.3 application on the original chosen orbit.
Every chosen-module, rank-one, non-FF, and concrete Suzuki-quotient hypothesis
is retained. These are the initial 7.3.2 bounds; the stronger Section 7.4
estimate and the final Suzuki exclusion remain with their source argument.

Source: Aschbacher--Smith E.6.3 and 7.3.2, printed pp.245,698.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The initial 7.3.2 parameters on the original Suzuki orbit, with the
finite quasisimple Held-cover theorem supplied. -/
theorem sourceOrbit_suzuki_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    ((2 * (2 * m + 1) : ℕ) : ℕ∞) ≤ ChapterE.globalR D.sourceOrbit ∧
      ChapterE.globalS D.sourceOrbit = (ChapterE.localM D.sourceOrbit : ℕ∞) ∧
      2 < ChapterE.globalS D.sourceOrbit :=
  D.sourceOrbit_suzuki_initial_parameters_of_held_center
    (fun _ _ _ _ => Held.CentralCovers.odd_center) h hmany hV hs hnon hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
