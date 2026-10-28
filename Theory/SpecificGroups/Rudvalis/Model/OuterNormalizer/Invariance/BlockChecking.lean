module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.Networks
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.Rows
/-!
# Blockwise finite checking for the Rudvalis orbital

The certificates check both routing circuits against the actual generators
and both packed-row transformation identities. Blocks of 64 letters bound
kernel memory use. The final block wraps modulo 4060; the soundness lemma
shows that all letters are covered. No numerical check is assumed.

Sources: the ATLAS tables documented in `Model.PermutationData` and the
rank-three action in GLS3, Table 5.3r, printed p.279.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

@[expose] public def checkBlock (P : Fin 4060 → Prop) [DecidablePred P] (b : Nat) : Bool :=
  Data.checkNat (fun k => decide (P ⟨(64 * b + k) % 4060, Nat.mod_lt _ (by decide)⟩)) 64

private theorem checkNat_sound (f : Nat → Bool) (n : Nat)
    (h : Data.checkNat f n = true) (k : Nat) (hk : k < n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Data.checkNat, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 hk
    · exact h.2

public theorem allFinBlocks (P : Fin 4060 → Prop) [DecidablePred P]
    (h : ∀ b : Fin 64, checkBlock P b.val = true) : ∀ x, P x := by
  intro x
  have hb : x.val / 64 < 64 := by omega
  have h' := checkNat_sound _ 64 (h ⟨x.val / 64, hb⟩) (x.val % 64) (Nat.mod_lt _ (by decide))
  have hx : 64 * (x.val / 64) + x.val % 64 = x.val := by omega
  simpa only [hx, Nat.mod_eq_of_lt x.isLt, Fin.eta] using of_decide_eq_true h'

@[expose] public def facts (x : Fin 4060) : Prop :=
  route aCircuit x.val = some (Data.aMap x).val ∧
  route bCircuit x.val = some (Data.bMap x).val ∧
  eval aCircuit (row (Data.aMap x)) = row x ∧
  eval bCircuit (row (Data.bMap x)) = row x

public instance (x : Fin 4060) : Decidable (facts x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Rudvalis.OuterNormalizer.InvarianceCertificate
