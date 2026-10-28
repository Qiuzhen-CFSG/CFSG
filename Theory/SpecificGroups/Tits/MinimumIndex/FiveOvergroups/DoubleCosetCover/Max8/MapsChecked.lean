module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.MapChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Ranges

import Mathlib.Tactic.FinCases

/-!
# Certification of the max8 point maps

Kernel reductions in ranges of 128 points establish equality with the
literal ATLAS generator words and the fixed double-coset representatives.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8

open Atlas1600OrderCertificate MinimumIndexCandidates
set_option Elab.async false
set_option maxRecDepth 20000

private theorem gen0_spec : ∀ p, genMaps 0 p = (gen max8Generators 0).val p := by
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

private theorem gen1_spec : ∀ p, genMaps 1 p = (gen max8Generators 1).val p := by
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

private theorem gen2_spec : ∀ p, genMaps 2 p = (gen max8Generators 2).val p := by
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

private theorem gen3_spec : ∀ p, genMaps 3 p = (gen max8Generators 3).val p := by
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
    genMaps i p = (gen max8Generators i).val p := by
  fin_cases i
  · exact gen0_spec p
  · exact gen1_spec p
  · exact gen2_spec p
  · exact gen3_spec p

private theorem rep0_spec : ∀ p, repMaps 0 p = (max8Rep 0).val p := by
  have h : ∀ p, repMaps 0 p = ((max8Word 0).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep1_spec : ∀ p, repMaps 1 p = (max8Rep 1).val p := by
  have h : ∀ p, repMaps 1 p = ((max8Word 1).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep2_spec : ∀ p, repMaps 2 p = (max8Rep 2).val p := by
  have h : ∀ p, repMaps 2 p = ((max8Word 2).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep3_spec : ∀ p, repMaps 3 p = (max8Rep 3).val p := by
  have h : ∀ p, repMaps 3 p = ((max8Word 3).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep4_spec : ∀ p, repMaps 4 p = (max8Rep 4).val p := by
  have h : ∀ p, repMaps 4 p = ((max8Word 4).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep5_spec : ∀ p, repMaps 5 p = (max8Rep 5).val p := by
  have h : ∀ p, repMaps 5 p = ((max8Word 5).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep6_spec : ∀ p, repMaps 6 p = (max8Rep 6).val p := by
  have h : ∀ p, repMaps 6 p = ((max8Word 6).map packedLetter).prod p := by
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
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep7_spec : ∀ p, repMaps 7 p = (max8Rep 7).val p := by
  have h : ∀ p, repMaps 7 p = ((max8Word 7).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep7Check0
    · exact rep7Check1
    · exact rep7Check2
    · exact rep7Check3
    · exact rep7Check4
    · exact rep7Check5
    · exact rep7Check6
    · exact rep7Check7
    · exact rep7Check8
    · exact rep7Check9
    · exact rep7Check10
    · exact rep7Check11
    · exact rep7Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep8_spec : ∀ p, repMaps 8 p = (max8Rep 8).val p := by
  have h : ∀ p, repMaps 8 p = ((max8Word 8).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep8Check0
    · exact rep8Check1
    · exact rep8Check2
    · exact rep8Check3
    · exact rep8Check4
    · exact rep8Check5
    · exact rep8Check6
    · exact rep8Check7
    · exact rep8Check8
    · exact rep8Check9
    · exact rep8Check10
    · exact rep8Check11
    · exact rep8Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep9_spec : ∀ p, repMaps 9 p = (max8Rep 9).val p := by
  have h : ∀ p, repMaps 9 p = ((max8Word 9).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep9Check0
    · exact rep9Check1
    · exact rep9Check2
    · exact rep9Check3
    · exact rep9Check4
    · exact rep9Check5
    · exact rep9Check6
    · exact rep9Check7
    · exact rep9Check8
    · exact rep9Check9
    · exact rep9Check10
    · exact rep9Check11
    · exact rep9Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep10_spec : ∀ p, repMaps 10 p = (max8Rep 10).val p := by
  have h : ∀ p, repMaps 10 p = ((max8Word 10).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep10Check0
    · exact rep10Check1
    · exact rep10Check2
    · exact rep10Check3
    · exact rep10Check4
    · exact rep10Check5
    · exact rep10Check6
    · exact rep10Check7
    · exact rep10Check8
    · exact rep10Check9
    · exact rep10Check10
    · exact rep10Check11
    · exact rep10Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep11_spec : ∀ p, repMaps 11 p = (max8Rep 11).val p := by
  have h : ∀ p, repMaps 11 p = ((max8Word 11).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep11Check0
    · exact rep11Check1
    · exact rep11Check2
    · exact rep11Check3
    · exact rep11Check4
    · exact rep11Check5
    · exact rep11Check6
    · exact rep11Check7
    · exact rep11Check8
    · exact rep11Check9
    · exact rep11Check10
    · exact rep11Check11
    · exact rep11Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep12_spec : ∀ p, repMaps 12 p = (max8Rep 12).val p := by
  have h : ∀ p, repMaps 12 p = ((max8Word 12).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep12Check0
    · exact rep12Check1
    · exact rep12Check2
    · exact rep12Check3
    · exact rep12Check4
    · exact rep12Check5
    · exact rep12Check6
    · exact rep12Check7
    · exact rep12Check8
    · exact rep12Check9
    · exact rep12Check10
    · exact rep12Check11
    · exact rep12Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep13_spec : ∀ p, repMaps 13 p = (max8Rep 13).val p := by
  have h : ∀ p, repMaps 13 p = ((max8Word 13).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep13Check0
    · exact rep13Check1
    · exact rep13Check2
    · exact rep13Check3
    · exact rep13Check4
    · exact rep13Check5
    · exact rep13Check6
    · exact rep13Check7
    · exact rep13Check8
    · exact rep13Check9
    · exact rep13Check10
    · exact rep13Check11
    · exact rep13Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep14_spec : ∀ p, repMaps 14 p = (max8Rep 14).val p := by
  have h : ∀ p, repMaps 14 p = ((max8Word 14).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep14Check0
    · exact rep14Check1
    · exact rep14Check2
    · exact rep14Check3
    · exact rep14Check4
    · exact rep14Check5
    · exact rep14Check6
    · exact rep14Check7
    · exact rep14Check8
    · exact rep14Check9
    · exact rep14Check10
    · exact rep14Check11
    · exact rep14Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep15_spec : ∀ p, repMaps 15 p = (max8Rep 15).val p := by
  have h : ∀ p, repMaps 15 p = ((max8Word 15).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep15Check0
    · exact rep15Check1
    · exact rep15Check2
    · exact rep15Check3
    · exact rep15Check4
    · exact rep15Check5
    · exact rep15Check6
    · exact rep15Check7
    · exact rep15Check8
    · exact rep15Check9
    · exact rep15Check10
    · exact rep15Check11
    · exact rep15Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep16_spec : ∀ p, repMaps 16 p = (max8Rep 16).val p := by
  have h : ∀ p, repMaps 16 p = ((max8Word 16).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep16Check0
    · exact rep16Check1
    · exact rep16Check2
    · exact rep16Check3
    · exact rep16Check4
    · exact rep16Check5
    · exact rep16Check6
    · exact rep16Check7
    · exact rep16Check8
    · exact rep16Check9
    · exact rep16Check10
    · exact rep16Check11
    · exact rep16Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep17_spec : ∀ p, repMaps 17 p = (max8Rep 17).val p := by
  have h : ∀ p, repMaps 17 p = ((max8Word 17).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep17Check0
    · exact rep17Check1
    · exact rep17Check2
    · exact rep17Check3
    · exact rep17Check4
    · exact rep17Check5
    · exact rep17Check6
    · exact rep17Check7
    · exact rep17Check8
    · exact rep17Check9
    · exact rep17Check10
    · exact rep17Check11
    · exact rep17Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep18_spec : ∀ p, repMaps 18 p = (max8Rep 18).val p := by
  have h : ∀ p, repMaps 18 p = ((max8Word 18).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep18Check0
    · exact rep18Check1
    · exact rep18Check2
    · exact rep18Check3
    · exact rep18Check4
    · exact rep18Check5
    · exact rep18Check6
    · exact rep18Check7
    · exact rep18Check8
    · exact rep18Check9
    · exact rep18Check10
    · exact rep18Check11
    · exact rep18Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep19_spec : ∀ p, repMaps 19 p = (max8Rep 19).val p := by
  have h : ∀ p, repMaps 19 p = ((max8Word 19).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep19Check0
    · exact rep19Check1
    · exact rep19Check2
    · exact rep19Check3
    · exact rep19Check4
    · exact rep19Check5
    · exact rep19Check6
    · exact rep19Check7
    · exact rep19Check8
    · exact rep19Check9
    · exact rep19Check10
    · exact rep19Check11
    · exact rep19Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep20_spec : ∀ p, repMaps 20 p = (max8Rep 20).val p := by
  have h : ∀ p, repMaps 20 p = ((max8Word 20).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep20Check0
    · exact rep20Check1
    · exact rep20Check2
    · exact rep20Check3
    · exact rep20Check4
    · exact rep20Check5
    · exact rep20Check6
    · exact rep20Check7
    · exact rep20Check8
    · exact rep20Check9
    · exact rep20Check10
    · exact rep20Check11
    · exact rep20Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep21_spec : ∀ p, repMaps 21 p = (max8Rep 21).val p := by
  have h : ∀ p, repMaps 21 p = ((max8Word 21).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep21Check0
    · exact rep21Check1
    · exact rep21Check2
    · exact rep21Check3
    · exact rep21Check4
    · exact rep21Check5
    · exact rep21Check6
    · exact rep21Check7
    · exact rep21Check8
    · exact rep21Check9
    · exact rep21Check10
    · exact rep21Check11
    · exact rep21Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep22_spec : ∀ p, repMaps 22 p = (max8Rep 22).val p := by
  have h : ∀ p, repMaps 22 p = ((max8Word 22).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep22Check0
    · exact rep22Check1
    · exact rep22Check2
    · exact rep22Check3
    · exact rep22Check4
    · exact rep22Check5
    · exact rep22Check6
    · exact rep22Check7
    · exact rep22Check8
    · exact rep22Check9
    · exact rep22Check10
    · exact rep22Check11
    · exact rep22Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep23_spec : ∀ p, repMaps 23 p = (max8Rep 23).val p := by
  have h : ∀ p, repMaps 23 p = ((max8Word 23).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep23Check0
    · exact rep23Check1
    · exact rep23Check2
    · exact rep23Check3
    · exact rep23Check4
    · exact rep23Check5
    · exact rep23Check6
    · exact rep23Check7
    · exact rep23Check8
    · exact rep23Check9
    · exact rep23Check10
    · exact rep23Check11
    · exact rep23Check12
  simpa only [packedWord_spec, max8Rep] using h

private theorem rep24_spec : ∀ p, repMaps 24 p = (max8Rep 24).val p := by
  have h : ∀ p, repMaps 24 p = ((max8Word 24).map packedLetter).prod p := by
    apply all_of_blocks (n := 1600) (k := 128) (b := 13) (by decide)
    intro block
    fin_cases block
    · exact rep24Check0
    · exact rep24Check1
    · exact rep24Check2
    · exact rep24Check3
    · exact rep24Check4
    · exact rep24Check5
    · exact rep24Check6
    · exact rep24Check7
    · exact rep24Check8
    · exact rep24Check9
    · exact rep24Check10
    · exact rep24Check11
    · exact rep24Check12
  simpa only [packedWord_spec, max8Rep] using h

public theorem repMaps_spec (i : Fin 25) (p : Fin 1600) :
    repMaps i p = (max8Rep i).val p := by
  fin_cases i
  · exact rep0_spec p
  · exact rep1_spec p
  · exact rep2_spec p
  · exact rep3_spec p
  · exact rep4_spec p
  · exact rep5_spec p
  · exact rep6_spec p
  · exact rep7_spec p
  · exact rep8_spec p
  · exact rep9_spec p
  · exact rep10_spec p
  · exact rep11_spec p
  · exact rep12_spec p
  · exact rep13_spec p
  · exact rep14_spec p
  · exact rep15_spec p
  · exact rep16_spec p
  · exact rep17_spec p
  · exact rep18_spec p
  · exact rep19_spec p
  · exact rep20_spec p
  · exact rep21_spec p
  · exact rep22_spec p
  · exact rep23_spec p
  · exact rep24_spec p

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8
