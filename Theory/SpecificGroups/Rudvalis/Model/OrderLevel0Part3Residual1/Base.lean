module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Generator comparisons for residual group 1

The seven distinct leaf tables agree with the already certified generator actions.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem base0 : ∀ x, Part6Tables.gen0 0 x = map0 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base1 : ∀ x, Part6Tables.gen0 1 x = map1 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base2 : ∀ x, Part6Tables.gen0 2 x = map2 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base3 : ∀ x, Part6Tables.gen0 3 x = map3 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base4 : ∀ x, Part6Tables.gen1 0 x = map4 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base5 : ∀ x, Part6Tables.gen1 1 x = map5 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base6 : ∀ x, Part6Tables.gen1 2 x = map6 x := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem base7 : ∀ x, Part6Tables.gen1 3 x = map7 x := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
