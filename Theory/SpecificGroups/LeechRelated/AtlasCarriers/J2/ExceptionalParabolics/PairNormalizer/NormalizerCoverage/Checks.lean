module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage.Data

/-!
# Finite checks for the J₂ normalizer cover

The word tree evaluates the coset representatives. Each of the 1575 signed
letter transitions has a factor given by a short word in the candidate.
Three point evaluations distinguish the selected conjugate of a radical
generator from every radical element for each nonidentity representative.
All finite identities are checked by the kernel; the group argument is in
`Words` and `NormalizerCoverage`.
Source: ATLAS J2G1-p100B0; GLS3 Table 5.3g. See `source/generate.py`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
open Theory.GroupTheory GeneratorPair GeneratorPair.FirstFusion
open GeneratorPair.SecondOrbitCertificate RadicalData SylowData QuotientData Data

/-- Permutation tables for the nine generators used in transition factors. -/
def factorGeneratorTable : Fin 9 → Equiv.Perm (Fin 100) :=
  ![qGenTable 0, qGenTable 1, qGenTable 2, qGenTable 3, qGenTable 4, qGenTable 5,
    sGenTable 3, oddTable 0, oddTable 1]

set_option maxRecDepth 100000 in
theorem factor_word_check : ∀ i p,
    evalWord factorGeneratorTable (factorWord i) p = factorMap i p := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem repr_zero_check : ∀ p, reprMap 0 p = p := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem word_tree_check : ∀ i : Fin 525, i ≠ 0 →
    (parent i).val < i.val ∧
      reprWord i = reprWord (parent i) ++ [parentLetter i] := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem repr_tree_check : ∀ i : Fin 525, i ≠ 0 → ∀ p,
    reprMap i p = reprMap (parent i) (permLetter (parentLetter i) p) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem transition_check : ∀ i j p,
    reprMap i (permLetter j p) = factorMap (factor i j) (reprMap (next i j) p) := by
  apply allFin
  decide +kernel

/-- Only three coordinates are needed for the nonnormalization checks. -/
def fingerprint (f : Fin 100 → Fin 100) : Nat :=
  (f 0).val + 128 * ((f 1).val + 128 * (f 2).val)

set_option maxRecDepth 100000 in
theorem separation_check : ∀ i : Fin 525, i ≠ 0 → ∀ k : Fin 64,
    fingerprint (fun p => reprMap i (qGenTable (badGenerator i) p)) ≠
      fingerprint (fun p => qTable k (reprMap i p)) := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
