module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Certificate

/-!
# Initial numerical checks for the upper J3 B-row seeds

The first short block and first seed comparison exercise the complete checking
path on all 6156 points. Remaining blocks and seed batches use the same proved
interface in Certificate. The first seed is representative 4714.
Source: `Order/data/witnesses.json`, ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh

set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem blockSoundZero : ∀ x : Fin 6156,
    lookup (blockTable 0) x.val = run mixedNat (blockWords 0) x.val := by
  apply allFin
  decide +kernel

set_option maxRecDepth 40000 in
public theorem checkZero : Check 0 := by
  decide +kernel

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh
