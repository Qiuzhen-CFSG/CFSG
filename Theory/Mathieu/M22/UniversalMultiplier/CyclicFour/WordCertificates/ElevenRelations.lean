module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.BaseRelations

/-!
# The two order-eleven relations in the literal ATLAS action

The verified lookup actions of AB and ABABB are iterated eleven times on all
4928 points. Together with A² = B⁴ = 1, these are precisely the relations used
by the published perfectness reduction for the paired group.

Source application: Aschbacher–Smith I.1.1 and I.1.3(4).
-/

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

set_option maxRecDepth 20000 in
private theorem ab_eleven_checked : checkEq (iter (action ab) 11) id = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem ababb_eleven_checked : checkEq (iter (action ababb) 11) id = true := by
  decide +kernel

public theorem ab_eleven : (Data.aPerm * Data.bPerm) ^ 11 = 1 :=
  pow_eq_one_of_check _ _ ab_apply 11 ab_eleven_checked

public theorem ababb_eleven :
    (Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm * Data.bPerm) ^ 11 = 1 :=
  pow_eq_one_of_check _ _ ababb_apply 11 ababb_eleven_checked

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
