module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.Complete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcluded

/-!
# Applying both weak-closure bounds in the doubled-branch exclusion

The proved first and second weak-closure implications remove the w > 2
premise from the terminal E.3.35 argument. The original pure-intersection,
positive-w, nonsingular-centralizer, odd-fixed-space and generation inputs
remain explicit. Their discharge belongs to qt-d-1222-double-natural and
its existing centralizer producers; this module assumes no local action
model, offender contradiction, or first/second weak-closure conclusion.
Source: Aschbacher--Smith, 12.1.8--11, printed pp.792--794 (PDF809--811).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual terminal consumer with both weak-closure premises discharged
from the earlier source geometry and positive zeroth bound. -/
theorem doubleNatural_excluded_of_many_of_source_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hgen : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      generationParameter H = 2) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T →
    B.NonsingularCentralizers → B.OddFixedSpaces → False := by
  let := D.doubledOrbit_elementary h
  intro hp hw hc ho
  have hNM := D.doubledOrbit_normalizer_eq h B.orbit_eq
  have hr := B.globalR_ge hNM hc
  have hr' := B.globalR_ge_add_two hNM hc ho
  have hb := D.doubled_weakClosure_bounds_of_many h hmany B hp hw hr
  exact D.doubleNatural_excluded_of_many_of_parameters h hmany B (hb.2 hr') hr' hgen

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
