module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# First binary factor-cache certificate

The first shared word is `[1, 2]`. Its proposed cached action is checked at
all 4060 points against the composition of the two certified generator maps.
This is the kernel-checked template for the remaining independent certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp4 : CompositionCheck 0 := by
  change ∀ x : Fin 4060, m4 x.val = Part6Nat.force m1 (m2 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
