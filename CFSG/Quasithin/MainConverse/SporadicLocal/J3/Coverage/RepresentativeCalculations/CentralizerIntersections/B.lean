module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections.Data
import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for a J₃ centralizer intersection

The selected generators are checked on every letter. Positive words are
then checked at the separating pair, and explicit nonmembership witnesses
exclude all remaining rows of the exhaustive `CRep` enumeration.
Source: GLS 3, Table 5.3h, p.269, via the fixed ATLAS permutation model.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open OrderCertificate CentralizerCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false

public theorem detectionB : ∀ r : CIndex,
    (CRep r * fastBasis 1) 0 = (fastBasis 1 * CRep r) 0 → goodB r := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

public theorem positiveB : ∀ r : CIndex, goodB r →
    CRep r 0 = fastElementary (maskB r) 0 ∧
    CRep r 1 = fastElementary (maskB r) 1 := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
