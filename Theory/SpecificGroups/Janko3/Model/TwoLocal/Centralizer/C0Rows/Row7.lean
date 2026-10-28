module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row2

import Mathlib.Tactic.FinCases

/-!
# Transition certificate at level 0 of the C chain

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal.CentralizerCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

public theorem C0Step_row7 (r : Fin 16) :
    C0Gen 7 * C0Rep r = C0Rep (C0Act 7 r) * evalWord C1Gen (C0Factor 7 r) := by
  fin_cases r <;> exact C0Step_row2 _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
