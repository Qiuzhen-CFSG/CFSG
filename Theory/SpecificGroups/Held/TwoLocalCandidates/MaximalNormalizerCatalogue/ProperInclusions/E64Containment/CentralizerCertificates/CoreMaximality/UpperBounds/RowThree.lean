module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.UpperBounds.Counting

/-!
# Distinct centralizer cosets for Held row 3

The 14 short words below lie in the literal row-zero conjugate of max5.
Their conjugation images on actual row generators have distinct point-image
signatures. Kernel reduction certifies the signatures using the previously
checked permutation tables; strict monotonicity certifies their distinctness.
This bounds the full centralizer using its proved ambient containment.

Source: ATLAS HeG1-p2058B0 and HeG1-max5W1, the catalogue generator words,
and GLS3 Table 5.3p. `source/generate.py` supplies untrusted discovery only.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.UpperBounds.RowThree
open LocalPairs.SylowGeometry.Calculations

private def codes (i : Fin 14) : List ℤ :=
  (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then [2] else (if i.val < 2 then [2, -1, 2, -1] else [1, -2, -1])) else (if i.val < 5 then (if i.val < 4 then [-2, -1] else [1, 2, 1, -2]) else (if i.val < 6 then [] else [-2]))) else (if i.val < 10 then (if i.val < 8 then [-2, 1, -2] else (if i.val < 9 then [1, -2] else [2, 1, -2])) else (if i.val < 12 then (if i.val < 11 then [1] else [-1, 2, -1]) else (if i.val < 13 then [-1] else [2, -1]))))

private def tests : List (List ℤ × Fin 2058) :=
  [([-4, 2, 1, 2, -4, -2, -1, -2], 0), ([-4, 2, 1, 2, -4, -2, -1, -2], 1)]

private def key (i : Fin 14) : ℕ :=
  (#[1508, 37877, 39089, 688964, 689260, 1196856, 1197289, 2872332, 2995049, 2995377, 3389764, 3390672, 3560520, 3560729] : Array ℕ)[i.val]!

private theorem tests_mem : ∀ t ∈ tests, t.1 ∈ generatorWords 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem signature_check : ∀ i : Fin 14,
    fastFingerprint tests (fastWitness (codes i)) = key i := by
  decide +kernel

private theorem key_injective : Function.Injective key := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

/-- Every element of the full row-3 centralizer is included in this bound. -/
public theorem centralizer_card_le (hp : IsPGroup 2 representative) :
    Nat.card (Subgroup.centralizer (ambient 3 : Set He)) ≤ 1536 := by
  have hi : Function.Injective (fun i => fingerprint tests (witness (codes i) : He)) := by
    intro i k h
    apply key_injective
    simpa only [← fastFingerprint_eq, ← fastWitness_eq, signature_check] using h
  have h := mul_card_centralizer_le hp 3 tests tests_mem codes hi
  omega

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.UpperBounds.RowThree
