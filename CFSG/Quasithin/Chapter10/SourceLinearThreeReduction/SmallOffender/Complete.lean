module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.SuzukiExclusion

/-!
# Small-offender recognition with its independent half-Sylow input

All local recognition, reselection, crossed-centralization and small-corank
branches are discharged. The remaining Suzuki configuration contradicts the
actual two-factor FF classification on the literal full-module quotient.
Thus half-Sylow uniqueness suffices for the published small-offender contract,
including preservation of the full module and the lower bound w≥2.

This is conditional only on the earlier half-Sylow source theorem. Its producer
is qt-d-10-nona5-half-sylow-unique; its original module-choice premise is
ultimately discharged by qt-d-10-nona5-point-control. The small-offender source
assembly remains with qt-d-10-nona5-small-offender until that input is supplied.
The earlier SmallOffender.Source is imported by recognition, so this final
assembly is separate to preserve that public boundary without an import cycle.

Source: Aschbacher–Smith 10.2.12, pp.754–755. The literal parent application is
source_nonnormalReduction_of_point_generation_smallOffender, argument hsmall.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open SmallOffender SmallOffender.Recognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original small-offender contract, retaining only the independent earlier
half-Sylow theorem. Every local recognition and small-corank branch is proved. -/
theorem source_nonnormalSmallOffender_of_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T) : SourceNonnormalSmallOffenderAt T := by
  rcases nonnormalSmallOffender_or_quiet_suzuki_two_factors hhalf with hs | h
  · exact hs
  obtain ⟨L,D,g,c,hJ,hNL,m,hm,⟨e⟩,_⟩ := h
  exact (no_quiet_suzuki_smallOffender D c hJ hNL hm e).elim

end CFSG.Quasithin.Chapter10
