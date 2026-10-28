module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row0
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row1
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row2
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row3
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row4
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row5
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row6
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row7
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row8
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.C0Rows.Row9

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

public theorem C0Step (i : Fin 10) (r : Fin 16) :
    C0Gen i * C0Rep r = C0Rep (C0Act i r) * evalWord C1Gen (C0Factor i r) := by
  fin_cases i
  · exact C0Step_row0 r
  · exact C0Step_row1 r
  · exact C0Step_row2 r
  · exact C0Step_row3 r
  · exact C0Step_row4 r
  · exact C0Step_row5 r
  · exact C0Step_row6 r
  · exact C0Step_row7 r
  · exact C0Step_row8 r
  · exact C0Step_row9 r

public theorem C0H_card : Nat.card C0H = 16 * Nat.card C1H :=
  wordSubgroup_card_eq_mul_next C0Gen C0Inv C0Inv_spec
    C1Gen C1Inv C1Inv_spec C0Rep C0Act C0Factor
    1067 C0Point 0 C0Rep_mem C1H_le C0Rep_base
    C0Rep_point C0Point_injective C1H_fix C0Step

public theorem C0H_decompose (g : C0H) :
    ∃ r, ∃ k : C1H, (g : Equiv.Perm (Fin 6156)) = C0Rep r * k := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, ∃ k : C1H, evalWord C0Gen w = C0Rep r * k by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, 1, by simp only [evalWord, C0Rep_base, Subgroup.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨C0Act i r, ⟨evalWord C1Gen (C0Factor i r) * k,
      C1H.mul_mem ⟨_, rfl⟩ k.property⟩, ?_⟩
    change C0Gen i * evalWord C0Gen w = _
    rw [hk, ← mul_assoc, C0Step]
    exact mul_assoc _ _ _

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
