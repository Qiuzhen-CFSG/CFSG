module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Words
import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Checked conjugacy and sign actors for Held pair (true,0)

The actual Held words are compared using the certified four-point base.
Both directions of the conjugacy are checked; the actor formulas refer to
the marked plane basis. Sources and word conventions are in Words.lean.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair10

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem forward (k : Fin 4) :
    transporter true 0 * SylowGeometry.Calculations.generator k * (transporter true 0)⁻¹ =
      evalPowers (twoGenerator true 0) (forwardWord true 0 k) := by
  fin_cases k <;> apply eq_of_four_point_images <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem backward (k : Fin 4) :
    (transporter true 0)⁻¹ * twoGenerator true 0 k * transporter true 0 =
      evalPowers SylowGeometry.Calculations.generator (backwardWord true 0 k) := by
  fin_cases k <;> apply eq_of_four_point_images <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem actor_action (k l : Fin 2) :
    actor true 0 k * basisGenerator true 0 l * (actor true 0 k)⁻¹ =
      if l = k then (basisGenerator true 0 l)⁻¹ else basisGenerator true 0 l := by
  fin_cases k <;> fin_cases l <;> apply eq_of_four_point_images <;> decide +kernel

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Pair10
