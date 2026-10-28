module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.ConjugationChecks
import Mathlib.Tactic.FinCases

/-!
# Relative normality of the order-32 core candidate

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

private theorem Q0H_conj (i : Fin 10) (g : Equiv.Perm (Fin 6156)) (hg : g ∈ Q0H) :
    C0Gen i * g * (C0Gen i)⁻¹ ∈ Q0H := by
  obtain ⟨w, rfl⟩ := hg
  induction w with
  | nil => simpa only [evalWord, mul_one, mul_inv_cancel] using Q0H.one_mem
  | cons j w ih =>
    change (MulAut.conj (C0Gen i)) (Q0Gen j * evalWord Q0Gen w) ∈ Q0H
    rw [map_mul]
    have hq : C0Gen i * Q0Gen j * (C0Gen i)⁻¹ ∈ Q0H := by
      rw [QConj]
      exact ⟨_, rfl⟩
    exact Q0H.mul_mem hq ih

public theorem C0Gen_normalizes_Q0H (i : Fin 10) :
    C0Gen i ∈ Subgroup.normalizer (Q0H : Set (Equiv.Perm (Fin 6156))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact Q0H_conj i g
  · intro hg
    have h := Q0H_conj (C0Inv i) _ hg
    simpa only [C0Inv_spec, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel,
      mul_one] using h

public theorem C0H_le_normalizer_Q0H :
    C0H ≤ Subgroup.normalizer (Q0H : Set (Equiv.Perm (Fin 6156))) := by
  rintro g ⟨w, rfl⟩
  induction w with
  | nil => exact (Subgroup.normalizer _).one_mem
  | cons i w ih => exact (Subgroup.normalizer _).mul_mem (C0Gen_normalizes_Q0H i) ih

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
