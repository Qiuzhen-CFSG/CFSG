module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Soundness
import Mathlib.Tactic.FinCases

/-!
# Certified normalizer factorizations for rows 0–15

The kernel checks every one of the 144 factorizations in each of the first
sixteen point-orbit rows. The soundness theorem then gives equality in the
actual ATLAS group, with both displayed factors in the literal normalizer.
This discharges the lower half of the factor-test premise of
`coverage_of_finite_checks`; the other rows and geometry are assembled by
`Coverage`.

Source: the primary ATLAS generators and the unchanged representative codes;
see `Coverage/source/README.md` for provenance and word conventions.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate

section RowChecks

-- Full-row kernel reductions are checked sequentially to bound peak memory.
set_option Elab.async false

set_option maxRecDepth 20000 in
private theorem factorsLow_row00_checked : ∀ j : Fin 144, factorTest 0 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row01_checked : ∀ j : Fin 144, factorTest 1 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row02_checked : ∀ j : Fin 144, factorTest 2 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row03_checked : ∀ j : Fin 144, factorTest 3 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row04_checked : ∀ j : Fin 144, factorTest 4 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row05_checked : ∀ j : Fin 144, factorTest 5 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row06_checked : ∀ j : Fin 144, factorTest 6 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row07_checked : ∀ j : Fin 144, factorTest 7 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row08_checked : ∀ j : Fin 144, factorTest 8 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row09_checked : ∀ j : Fin 144, factorTest 9 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row10_checked : ∀ j : Fin 144, factorTest 10 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row11_checked : ∀ j : Fin 144, factorTest 11 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row12_checked : ∀ j : Fin 144, factorTest 12 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row13_checked : ∀ j : Fin 144, factorTest 13 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row14_checked : ∀ j : Fin 144, factorTest 14 j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem factorsLow_row15_checked : ∀ j : Fin 144, factorTest 15 j = true := by
  apply allFin
  decide +kernel

end RowChecks

/-- All 2304 factor tests in rows 0 through 15 hold without further premises. -/
public theorem factors_low_checked (i : Fin 32) (hi : i.val < 16) (j : Fin 144) :
    factorTest i j = true := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 16, i = k.castLE (by decide) :=
    ⟨⟨i.val, hi⟩, rfl⟩
  fin_cases k
  · exact factorsLow_row00_checked j
  · exact factorsLow_row01_checked j
  · exact factorsLow_row02_checked j
  · exact factorsLow_row03_checked j
  · exact factorsLow_row04_checked j
  · exact factorsLow_row05_checked j
  · exact factorsLow_row06_checked j
  · exact factorsLow_row07_checked j
  · exact factorsLow_row08_checked j
  · exact factorsLow_row09_checked j
  · exact factorsLow_row10_checked j
  · exact factorsLow_row11_checked j
  · exact factorsLow_row12_checked j
  · exact factorsLow_row13_checked j
  · exact factorsLow_row14_checked j
  · exact factorsLow_row15_checked j

/-- The checked tests give the displayed equality in the actual fixed group. -/
public theorem factors_low (i : Fin 32) (hi : i.val < 16) (j : Fin 144) :
    orbitRep i * stabilizerRep j =
      normalWord (factorLeft i j) * representative (factorRep i j) *
      normalWord (factorRight i j) :=
  factorTest_sound i j (factors_low_checked i hi j)

/-- Both factors are elements of the literal thirteen-normalizer. -/
public theorem factors_low_normalizer (i : Fin 32) (hi : i.val < 16) (j : Fin 144) :
    ∃ (a b : thirteenNormalizer),
      orbitRep i * stabilizerRep j = a.val * representative (factorRep i j) * b.val := by
  refine ⟨normalizerElement (factorLeft i j), normalizerElement (factorRight i j), ?_⟩
  exact factors_low i hi j

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
