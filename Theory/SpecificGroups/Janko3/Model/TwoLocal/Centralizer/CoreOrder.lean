module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q0Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q1Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q2Steps
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q3Steps
import Mathlib.Tactic.FinCases

/-!
# Order of the intrinsic core candidate

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

public theorem Q0H_order : Nat.card Q0H = 32 := by
  rw [Q0H_card, Q1H_card, Q2H_card, Q3H_card, Q4H, wordSubgroup_fin_zero_card]

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
