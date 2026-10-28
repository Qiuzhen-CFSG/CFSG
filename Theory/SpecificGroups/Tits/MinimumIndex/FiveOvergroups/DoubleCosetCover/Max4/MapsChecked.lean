module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.MapChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Ranges

import Mathlib.Tactic.FinCases

/-!
# Certification of the max4 point maps

Kernel reductions in ranges of 128 points establish equality with the
literal ATLAS generator words and the fixed double-coset representatives.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4

open Atlas1600OrderCertificate MinimumIndexCandidates
set_option Elab.async false
set_option maxRecDepth 20000

private theorem gen0_spec : ∀ p, genMaps 0 p = (gen max4Generators 0).val p := by
  have h : ∀ p, genMaps 0 p = packedGen 0 p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact gen0Check0
    · exact gen0Check1
    · exact gen0Check2
    · exact gen0Check3
    · exact gen0Check4
    · exact gen0Check5
    · exact gen0Check6
    · exact gen0Check7
    · exact gen0Check8
    · exact gen0Check9
    · exact gen0Check10
    · exact gen0Check11
    · exact gen0Check12
  simpa only [packedGen_spec] using h

private theorem gen1_spec : ∀ p, genMaps 1 p = (gen max4Generators 1).val p := by
  have h : ∀ p, genMaps 1 p = packedGen 1 p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact gen1Check0
    · exact gen1Check1
    · exact gen1Check2
    · exact gen1Check3
    · exact gen1Check4
    · exact gen1Check5
    · exact gen1Check6
    · exact gen1Check7
    · exact gen1Check8
    · exact gen1Check9
    · exact gen1Check10
    · exact gen1Check11
    · exact gen1Check12
  simpa only [packedGen_spec] using h

private theorem gen2_spec : ∀ p, genMaps 2 p = (gen max4Generators 2).val p := by
  have h : ∀ p, genMaps 2 p = packedGen 2 p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact gen2Check0
    · exact gen2Check1
    · exact gen2Check2
    · exact gen2Check3
    · exact gen2Check4
    · exact gen2Check5
    · exact gen2Check6
    · exact gen2Check7
    · exact gen2Check8
    · exact gen2Check9
    · exact gen2Check10
    · exact gen2Check11
    · exact gen2Check12
  simpa only [packedGen_spec] using h

private theorem gen3_spec : ∀ p, genMaps 3 p = (gen max4Generators 3).val p := by
  have h : ∀ p, genMaps 3 p = packedGen 3 p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact gen3Check0
    · exact gen3Check1
    · exact gen3Check2
    · exact gen3Check3
    · exact gen3Check4
    · exact gen3Check5
    · exact gen3Check6
    · exact gen3Check7
    · exact gen3Check8
    · exact gen3Check9
    · exact gen3Check10
    · exact gen3Check11
    · exact gen3Check12
  simpa only [packedGen_spec] using h

public theorem genMaps_spec (i : Fin 4) (p : Fin 1600) :
    genMaps i p = (gen max4Generators i).val p := by
  fin_cases i
  · exact gen0_spec p
  · exact gen1_spec p
  · exact gen2_spec p
  · exact gen3_spec p

private theorem rep0_spec : ∀ p, repMaps 0 p = (max4Rep 0).val p := by
  have h : ∀ p, repMaps 0 p = ((max4Word 0).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep0Check0
    · exact rep0Check1
    · exact rep0Check2
    · exact rep0Check3
    · exact rep0Check4
    · exact rep0Check5
    · exact rep0Check6
    · exact rep0Check7
    · exact rep0Check8
    · exact rep0Check9
    · exact rep0Check10
    · exact rep0Check11
    · exact rep0Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep1_spec : ∀ p, repMaps 1 p = (max4Rep 1).val p := by
  have h : ∀ p, repMaps 1 p = ((max4Word 1).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep1Check0
    · exact rep1Check1
    · exact rep1Check2
    · exact rep1Check3
    · exact rep1Check4
    · exact rep1Check5
    · exact rep1Check6
    · exact rep1Check7
    · exact rep1Check8
    · exact rep1Check9
    · exact rep1Check10
    · exact rep1Check11
    · exact rep1Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep2_spec : ∀ p, repMaps 2 p = (max4Rep 2).val p := by
  have h : ∀ p, repMaps 2 p = ((max4Word 2).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep2Check0
    · exact rep2Check1
    · exact rep2Check2
    · exact rep2Check3
    · exact rep2Check4
    · exact rep2Check5
    · exact rep2Check6
    · exact rep2Check7
    · exact rep2Check8
    · exact rep2Check9
    · exact rep2Check10
    · exact rep2Check11
    · exact rep2Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep3_spec : ∀ p, repMaps 3 p = (max4Rep 3).val p := by
  have h : ∀ p, repMaps 3 p = ((max4Word 3).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep3Check0
    · exact rep3Check1
    · exact rep3Check2
    · exact rep3Check3
    · exact rep3Check4
    · exact rep3Check5
    · exact rep3Check6
    · exact rep3Check7
    · exact rep3Check8
    · exact rep3Check9
    · exact rep3Check10
    · exact rep3Check11
    · exact rep3Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep4_spec : ∀ p, repMaps 4 p = (max4Rep 4).val p := by
  have h : ∀ p, repMaps 4 p = ((max4Word 4).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep4Check0
    · exact rep4Check1
    · exact rep4Check2
    · exact rep4Check3
    · exact rep4Check4
    · exact rep4Check5
    · exact rep4Check6
    · exact rep4Check7
    · exact rep4Check8
    · exact rep4Check9
    · exact rep4Check10
    · exact rep4Check11
    · exact rep4Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep5_spec : ∀ p, repMaps 5 p = (max4Rep 5).val p := by
  have h : ∀ p, repMaps 5 p = ((max4Word 5).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep5Check0
    · exact rep5Check1
    · exact rep5Check2
    · exact rep5Check3
    · exact rep5Check4
    · exact rep5Check5
    · exact rep5Check6
    · exact rep5Check7
    · exact rep5Check8
    · exact rep5Check9
    · exact rep5Check10
    · exact rep5Check11
    · exact rep5Check12
  simpa only [packedWord_spec, max4Rep] using h

private theorem rep6_spec : ∀ p, repMaps 6 p = (max4Rep 6).val p := by
  have h : ∀ p, repMaps 6 p = ((max4Word 6).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep6Check0
    · exact rep6Check1
    · exact rep6Check2
    · exact rep6Check3
    · exact rep6Check4
    · exact rep6Check5
    · exact rep6Check6
    · exact rep6Check7
    · exact rep6Check8
    · exact rep6Check9
    · exact rep6Check10
    · exact rep6Check11
    · exact rep6Check12
  simpa only [packedWord_spec, max4Rep] using h

public theorem repMaps_spec (i : Fin 7) (p : Fin 1600) :
    repMaps i p = (max4Rep i).val p := by
  fin_cases i
  · exact rep0_spec p
  · exact rep1_spec p
  · exact rep2_spec p
  · exact rep3_spec p
  · exact rep4_spec p
  · exact rep5_spec p
  · exact rep6_spec p

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4
