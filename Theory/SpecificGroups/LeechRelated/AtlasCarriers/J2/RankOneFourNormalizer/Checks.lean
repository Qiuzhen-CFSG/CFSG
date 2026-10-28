module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Checks

/-!
# Finite checks for the normal four-group of the Hall–Janko Sylow subgroup

An involution commuting with its conjugates by the seven Sylow generators
has index 0, 5, 6 or 26 in the existing 128-element enumeration. These four
entries centralize the radical. The existing 525 normalizer cosets separate
its center from every nonidentity coset. Finally the eighteen radical cosets
exclude centralizers outside the radical, using just two permutation points.

All checks reduce in the kernel on the unchanged ATLAS J2G1-p100B0 tables.
No new enumeration or externally trusted certificate is used. The last check
is the inner-group specialization of NormalizerAction/PointwiseFixer.lean.
Source: GLS3 Table 5.3g; Aschbacher–Smith, 15.3.43, printed p.1140.
The retained ATLAS attribution is in AtlasCarriers/source/; original proof
code is Apache 2.0, as in the repository LICENSE.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RankOneFourNormalizer.Checks
open Theory.GroupTheory ExceptionalParabolics GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.SylowData
open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
theorem normal_element_check : ∀ i : Fin 128,
    (sTable i * sTable i) 0 = 0 → (sTable i * sTable i) 1 = 1 →
    (∀ j : Fin 7,
      let c := sGenTable j * sTable i * (sGenTable j)⁻¹
      (sTable i * c) 0 = (c * sTable i) 0 ∧
      (sTable i * c) 1 = (c * sTable i) 1) →
    i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26 := by
  apply allFin
  decide +kernel

def fourIndex : Fin 4 → Fin 64 := ![0, 5, 6, 26]

set_option maxRecDepth 100000 in
theorem four_central_check : ∀ i : Fin 4, ∀ j : Fin 6,
    qGenTable j * qTable (fourIndex i) = qTable (fourIndex i) * qGenTable j := by
  apply allFin
  decide +kernel

open PairNormalizer.NormalizerCoverage in
set_option maxRecDepth 100000 in
theorem four_separation_check : ∀ i : Fin 525, i ≠ 0 → ∃ j : Fin 4, ∀ k : Fin 4,
    fingerprint (fun p => Data.reprMap i (qTable (fourIndex j) p)) ≠
      fingerprint (fun p => qTable (fourIndex k) (Data.reprMap i p)) := by
  apply allFin
  decide +kernel

open PairNormalizer.CandidateQuotient in
set_option maxRecDepth 100000 in
theorem centralizer_check : ∀ i : Fin 64, ∀ j : Fin 18,
    (∀ k : Fin 6,
      let p := qTable i * repTable j
      (p * qGenTable k) 0 = (qGenTable k * p) 0 ∧
      (p * qGenTable k) 1 = (qGenTable k * p) 1) → j = 0 := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.RankOneFourNormalizer.Checks
