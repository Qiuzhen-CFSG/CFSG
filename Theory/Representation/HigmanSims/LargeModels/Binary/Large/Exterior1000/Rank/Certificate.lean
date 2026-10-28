module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic

/-!
# Bounded certificates for the fixed inverse calculation

A certificate records the XOR total after each block. Checking each transition
uses only the bounded block and the next recorded total, so kernel reduction
never expands the full nested row product. Induction and `combine_append`
recover the ordinary packed product. The certificate and its generator are
untrusted; `combine_of_checkBlocks` requires a kernel proof of every check.

This checker supports the ATLAS HS section in `Binary/source/section1000.json`.
Source attribution and rights are retained in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Rank
open RowArithmetic

/-- Each certificate entry is the packed product of the remaining blocks. -/
def checkBlocks : List (List ℕ) → ℕ → ℕ → List ℕ → Bool
  | [], _, out, [] => out == 0
  | b :: bs, mask, out, next :: cert =>
      (combine b mask ^^^ next == out) && checkBlocks bs (mask >>> b.length) next cert
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
      exact h.1

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Rank
