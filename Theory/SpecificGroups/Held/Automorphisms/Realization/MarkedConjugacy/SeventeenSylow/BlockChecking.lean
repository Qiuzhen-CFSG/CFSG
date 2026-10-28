module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Networks

/-!
# Finite checking of Held graph preservation

Each block checks 64 vertices. At every vertex both routing circuits agree
with the actual Held generators, and both transformed graph rows agree with
the original rows. The last block wraps modulo 2058; the coverage proof
includes every vertex. The circuit soundness theorem converts these finite
equalities into preservation of the existing graph relation.

Source: the ATLAS HeG1-p2058B0 tables retained in `Held/Model/Source`.
The checking scheme follows the existing Rudvalis orbital certificate.
-/

namespace Held.Realization.MarkedConjugacy.Seventeen
open Held.NormalizerGraph Rudvalis.OuterNormalizer.InvarianceCertificate

@[expose] public def checkNat (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => checkNat f n && f n

@[expose] public def checkBlock (P : Fin 2058 → Prop) [DecidablePred P] (b : ℕ) : Bool :=
  checkNat (fun k => decide (P ⟨(64 * b + k) % 2058, Nat.mod_lt _ (by decide)⟩)) 64

private theorem checkNat_sound (f : ℕ → Bool) (n : ℕ)
    (h : checkNat f n = true) (k : ℕ) (hk : k < n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [checkNat, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 hk
    · exact h.2

public theorem allFinBlocks (P : Fin 2058 → Prop) [DecidablePred P]
    (h : ∀ b : Fin 33, checkBlock P b.val = true) : ∀ x, P x := by
  intro x
  have hb : x.val / 64 < 33 := by omega
  have h' := checkNat_sound _ 64 (h ⟨x.val / 64, hb⟩) (x.val % 64)
    (Nat.mod_lt _ (by decide))
  have hx : 64 * (x.val / 64) + x.val % 64 = x.val := by omega
  simpa only [hx, Nat.mod_eq_of_lt x.isLt, Fin.eta] using of_decide_eq_true h'

@[expose] public def facts (x : Fin 2058) : Prop :=
  route aCircuit x.val = some (atlasA x).val ∧
  route bCircuit x.val = some (atlasB x).val ∧
  eval aCircuit (rowMask (atlasA x)) = rowMask x ∧
  eval bCircuit (rowMask (atlasB x)) = rowMask x

public instance (x : Fin 2058) : Decidable (facts x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Held.Realization.MarkedConjugacy.Seventeen
