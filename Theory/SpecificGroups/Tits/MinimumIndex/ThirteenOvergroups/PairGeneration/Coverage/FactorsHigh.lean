module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Sample
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Soundness
import Mathlib.Tactic.IntervalCases

/-!
# Thirteen-normalizer factorizations for point-orbit rows 16–31

The kernel checks all 144 products in each of rows 16–30 against the fixed
ATLAS representative words. Row 31 reuses the certificate in `Coverage.Sample`.
These checks discharge the high-row part of the factorization premise in
`coverage_of_finite_checks`. Soundness gives the literal group factorization,
and both displayed factors belong to the actual thirteen-normalizer.

The expensive row declarations are checked sequentially to bound memory.
Source: the primary ATLAS Tits generators and unchanged representative codes;
see `Coverage/source/README.md` for provenance and multiplication conventions.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate

section RowChecks

-- A single full row already uses several GiB; do not overlap these checks.
set_option Elab.async false

set_option maxRecDepth 20000 in
private theorem factorHighRow16_checked : ∀ j : Fin 144, factorTest 16 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow17_checked : ∀ j : Fin 144, factorTest 17 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow18_checked : ∀ j : Fin 144, factorTest 18 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow19_checked : ∀ j : Fin 144, factorTest 19 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow20_checked : ∀ j : Fin 144, factorTest 20 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow21_checked : ∀ j : Fin 144, factorTest 21 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow22_checked : ∀ j : Fin 144, factorTest 22 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow23_checked : ∀ j : Fin 144, factorTest 23 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow24_checked : ∀ j : Fin 144, factorTest 24 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow25_checked : ∀ j : Fin 144, factorTest 25 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow26_checked : ∀ j : Fin 144, factorTest 26 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow27_checked : ∀ j : Fin 144, factorTest 27 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow28_checked : ∀ j : Fin 144, factorTest 28 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow29_checked : ∀ j : Fin 144, factorTest 29 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorHighRow30_checked : ∀ j : Fin 144, factorTest 30 j = true := by
  apply allFin
  decide +kernel

end RowChecks

/-- Every reduced product in the high sixteen point-orbit rows passes its test. -/
public theorem factors_high_checked (i : Fin 32) (hi : 16 ≤ i.val) (j : Fin 144) :
    factorTest i j = true := by
  rcases i with ⟨i, hlt⟩
  interval_cases i
  · exact factorHighRow16_checked j
  · exact factorHighRow17_checked j
  · exact factorHighRow18_checked j
  · exact factorHighRow19_checked j
  · exact factorHighRow20_checked j
  · exact factorHighRow21_checked j
  · exact factorHighRow22_checked j
  · exact factorHighRow23_checked j
  · exact factorHighRow24_checked j
  · exact factorHighRow25_checked j
  · exact factorHighRow26_checked j
  · exact factorHighRow27_checked j
  · exact factorHighRow28_checked j
  · exact factorHighRow29_checked j
  · exact factorHighRow30_checked j
  · exact factorRow31_checked j

/-- The checked high rows factor through the fixed representatives, with both
literal factors certified to lie in the actual thirteen-normalizer. -/
public theorem factors_high (i : Fin 32) (hi : 16 ≤ i.val) (j : Fin 144) :
    normalWord (factorLeft i j) ∈ thirteenNormalizer ∧
    normalWord (factorRight i j) ∈ thirteenNormalizer ∧
    orbitRep i * stabilizerRep j =
      normalWord (factorLeft i j) * representative (factorRep i j) *
        normalWord (factorRight i j) :=
  ⟨normalWord_mem _, normalWord_mem _,
    factorTest_sound i j (factors_high_checked i hi j)⟩

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
