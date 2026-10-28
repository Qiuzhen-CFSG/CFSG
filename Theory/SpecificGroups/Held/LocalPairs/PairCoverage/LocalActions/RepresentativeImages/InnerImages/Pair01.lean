module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Words
import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugacy and sign actors for Held pair (false,1)

The actual Held words are compared using the certified four-point base.
Both directions of the conjugacy are checked; the actor formulas refer to
the marked plane basis. Sources and word conventions are in Words.lean.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair01

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem forward (k : Fin 4) :
    transporter false 1 * SylowGeometry.Calculations.generator k * (transporter false 1)⁻¹ =
      evalPowers (twoGenerator false 1) (forwardWord false 1 k) := by
  fin_cases k <;> apply eq_of_four_point_images <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem backward (k : Fin 4) :
    (transporter false 1)⁻¹ * twoGenerator false 1 k * transporter false 1 =
      evalPowers SylowGeometry.Calculations.generator (backwardWord false 1 k) := by
  fin_cases k <;> apply eq_of_four_point_images <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem actor_action (k l : Fin 2) :
    actor false 1 k * basisGenerator false 1 l * (actor false 1 k)⁻¹ =
      if l = k then (basisGenerator false 1 l)⁻¹ else basisGenerator false 1 l := by
  fin_cases k <;> fin_cases l <;> apply eq_of_four_point_images <;> decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair01
