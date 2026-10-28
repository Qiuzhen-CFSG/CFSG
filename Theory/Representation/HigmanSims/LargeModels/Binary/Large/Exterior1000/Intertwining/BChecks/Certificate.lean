module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Tables
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data1000

/-!
# Bounded product certificates for the second exterior generator

Each trace entry is the XOR total of the remaining blocks. The checker verifies
one short block against that next total. Induction with `combine_append` recovers
the complete product; `combine_mod` permits truncating each block's input mask.
The generated traces are untrusted inputs, and every check is proved by Lean's
kernel. `Blocks` aligns the lists with the existing fixed trees, and the row
modules use this theorem to prove the literal second-generator products.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and
`Binary/source/section1000.json`. Attribution and rights are retained in
`Binary/source/README.md`. Original repository code under Apache 2.0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.BChecks
open RowArithmetic

def checkBlocks : List (List ℕ) → ℕ → ℕ → List ℕ → Bool
  | [], _, out, [] => out == 0
  | b :: bs, mask, out, next :: cert =>
      (combine b (mask % 2 ^ b.length) ^^^ next == out) &&
        checkBlocks bs (mask >>> b.length) next cert
  | _, _, _, _ => false

theorem combine_of_checkBlocks (blocks : List (List ℕ)) (mask out : ℕ) (cert : List ℕ)
    (h : checkBlocks blocks mask out cert = true) :
    combine blocks.flatten mask = out := by
  induction blocks generalizing mask out cert with
  | nil =>
    cases cert with
    | nil =>
      have h0 : out = 0 := by simpa only [checkBlocks, beq_iff_eq] using h
      exact h0.symm
    | cons c cs => simp [checkBlocks] at h
  | cons b bs ih =>
    cases cert with
    | nil => simp [checkBlocks] at h
    | cons next cert =>
      simp only [checkBlocks, Bool.and_eq_true, beq_iff_eq] at h
      rw [List.flatten_cons, combine_append, ih _ _ _ h.2]
      rw [combine_mod] at h
      exact h.1
end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.BChecks
