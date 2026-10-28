module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.FactorSets
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.Reduction
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.TwelveCertificate
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.SixCertificate

/-!
# Second cohomology for the two additional binary S4 actions

Every normalized factor set for the twelve-orbit action is a coboundary.
For the six-orbit action any two non-coboundaries are cohomologous.

The certificates eliminate the normalized cocycle equations, leaving 89 free
binary coordinates in each case. Explicit correcting cochains kill all of
those coordinates in the first case, and leave a single scalar obstruction
in the second. Two non-coboundaries have obstruction 1, so their product has
obstruction 0 and supplies the required change of section. The finite checks
use kernel reduction; the Python generator is not trusted.

These statements supply the cohomology inputs to the extension argument for
Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314. They concern the
exact actions in `NonsplitAlternatives.Actions` and require no ambient group
or model realization.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
open Cohomology

/-- The second cohomology of the twelve-orbit binary action vanishes. -/
public theorem twelveOrbit_isCoboundary (c : FactorSet twelveOrbitAction) :
    c.IsCoboundary := by
  apply coboundary_of_certificate twelveOrbitColumns twelveOrbitAction_apply
    Twelve.steps Twelve.valid Twelve.pivots Twelve.covers Twelve.cochain
    Twelve.cochain_zero Twelve.obstruction Twelve.free c
  exact ev_zero _

private theorem sixOrbit_isCoboundary_of_obstruction_zero (c : FactorSet sixOrbitAction)
    (hc : ev (coordinates c) Six.obstruction = 0) : c.IsCoboundary :=
  coboundary_of_certificate sixOrbitColumns sixOrbitAction_apply
    Six.steps Six.valid Six.pivots Six.covers Six.cochain
    Six.cochain_zero Six.obstruction Six.free c hc

/-- All nonzero second-cohomology classes for the six-orbit action coincide. -/
public theorem sixOrbit_cohomologous_of_not_isCoboundary (c d : FactorSet sixOrbitAction)
    (hc : ¬ c.IsCoboundary) (hd : ¬ d.IsCoboundary) : c.Cohomologous d := by
  have binary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  have hc1 : ev (coordinates c) Six.obstruction = 1 :=
    (binary _).resolve_left (fun h => hc (sixOrbit_isCoboundary_of_obstruction_zero c h))
  have hd1 : ev (coordinates d) Six.obstruction = 1 :=
    (binary _).resolve_left (fun h => hd (sixOrbit_isCoboundary_of_obstruction_zero d h))
  apply cohomologous_of_times_isCoboundary
  apply sixOrbit_isCoboundary_of_obstruction_zero
  rw [coordinates_times, ev_add, hc1, hd1]
  decide +kernel

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
