module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementaryComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Data
import Mathlib.Tactic.FinCases

/-!
# Conjugation of the marked Rudvalis eight-group basis

The two actual max4 generators send the three basis elements to words in
that same basis. Every equality is checked on all 4060 points, in sixteen
bounded blocks to keep kernel memory use small, then transferred through
the faithful inclusion of the original model. Two involution identities and
the commuting relation also identify the four words of the marked plane.

Source: Wilson–Nickerson–Bray, ATLAS of Finite Group Representations,
`RuG1-max4W1`, attributed in `SylowOvergroups.Definitions`, with the fixed
words in `LocalCover.Data`. The application is Aschbacher–Smith, 15.3.43,
printed p.1140, and GLS3 Table 5.3r. The original words and data are unchanged;
all finite certificates below are kernel checked.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightAction
open CatalogueCertificate Max4Normalizers Max4Normalizers.GeneratorMaps
set_option maxRecDepth 30000
set_option Elab.async false

private theorem first_conj_zero_chunk0 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 0 = true := by
  decide +kernel

private theorem first_conj_zero_chunk1 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 1 = true := by
  decide +kernel

private theorem first_conj_zero_chunk2 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 2 = true := by
  decide +kernel

private theorem first_conj_zero_chunk3 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 3 = true := by
  decide +kernel

private theorem first_conj_zero_chunk4 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 4 = true := by
  decide +kernel

private theorem first_conj_zero_chunk5 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 5 = true := by
  decide +kernel

private theorem first_conj_zero_chunk6 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 6 = true := by
  decide +kernel

private theorem first_conj_zero_chunk7 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 7 = true := by
  decide +kernel

private theorem first_conj_zero_chunk8 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 8 = true := by
  decide +kernel

private theorem first_conj_zero_chunk9 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 9 = true := by
  decide +kernel

private theorem first_conj_zero_chunk10 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 10 = true := by
  decide +kernel

private theorem first_conj_zero_chunk11 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 11 = true := by
  decide +kernel

private theorem first_conj_zero_chunk12 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 12 = true := by
  decide +kernel

private theorem first_conj_zero_chunk13 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 13 = true := by
  decide +kernel

private theorem first_conj_zero_chunk14 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 14 = true := by
  decide +kernel

private theorem first_conj_zero_chunk15 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 0 * (gen 0)⁻¹) x = (elementaryPermutation 0) x) 15 = true := by
  decide +kernel

private theorem first_conj_zero_table : gen 0 * elementaryPermutation 0 * (gen 0)⁻¹ = elementaryPermutation 0 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact first_conj_zero_chunk0
  · exact first_conj_zero_chunk1
  · exact first_conj_zero_chunk2
  · exact first_conj_zero_chunk3
  · exact first_conj_zero_chunk4
  · exact first_conj_zero_chunk5
  · exact first_conj_zero_chunk6
  · exact first_conj_zero_chunk7
  · exact first_conj_zero_chunk8
  · exact first_conj_zero_chunk9
  · exact first_conj_zero_chunk10
  · exact first_conj_zero_chunk11
  · exact first_conj_zero_chunk12
  · exact first_conj_zero_chunk13
  · exact first_conj_zero_chunk14
  · exact first_conj_zero_chunk15

/-- Conjugation of basis element 0 by max4 generator 1. -/
public theorem first_conj_zero :
    max4Generators.1 * elementaryGenerator 0 * max4Generators.1⁻¹ =
      elementaryGenerator 0 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.1 * modelSubgroup.subtype (elementaryGenerator 0) *
    (modelSubgroup.subtype max4Generators.1)⁻¹ = modelSubgroup.subtype (elementaryGenerator 0)
  simpa only [gen_eq, LocalCardinality.Max4.generator0_eq, elementaryPermutation_eq]
    using first_conj_zero_table

private theorem first_conj_one_chunk0 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 0 = true := by
  decide +kernel

private theorem first_conj_one_chunk1 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 1 = true := by
  decide +kernel

private theorem first_conj_one_chunk2 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 2 = true := by
  decide +kernel

private theorem first_conj_one_chunk3 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 3 = true := by
  decide +kernel

private theorem first_conj_one_chunk4 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 4 = true := by
  decide +kernel

private theorem first_conj_one_chunk5 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 5 = true := by
  decide +kernel

private theorem first_conj_one_chunk6 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 6 = true := by
  decide +kernel

private theorem first_conj_one_chunk7 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 7 = true := by
  decide +kernel

private theorem first_conj_one_chunk8 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 8 = true := by
  decide +kernel

private theorem first_conj_one_chunk9 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 9 = true := by
  decide +kernel

private theorem first_conj_one_chunk10 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 10 = true := by
  decide +kernel

private theorem first_conj_one_chunk11 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 11 = true := by
  decide +kernel

private theorem first_conj_one_chunk12 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 12 = true := by
  decide +kernel

private theorem first_conj_one_chunk13 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 13 = true := by
  decide +kernel

private theorem first_conj_one_chunk14 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 14 = true := by
  decide +kernel

private theorem first_conj_one_chunk15 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 1 * (gen 0)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2) x) 15 = true := by
  decide +kernel

private theorem first_conj_one_table : gen 0 * elementaryPermutation 1 * (gen 0)⁻¹ = elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact first_conj_one_chunk0
  · exact first_conj_one_chunk1
  · exact first_conj_one_chunk2
  · exact first_conj_one_chunk3
  · exact first_conj_one_chunk4
  · exact first_conj_one_chunk5
  · exact first_conj_one_chunk6
  · exact first_conj_one_chunk7
  · exact first_conj_one_chunk8
  · exact first_conj_one_chunk9
  · exact first_conj_one_chunk10
  · exact first_conj_one_chunk11
  · exact first_conj_one_chunk12
  · exact first_conj_one_chunk13
  · exact first_conj_one_chunk14
  · exact first_conj_one_chunk15

/-- Conjugation of basis element 1 by max4 generator 1. -/
public theorem first_conj_one :
    max4Generators.1 * elementaryGenerator 1 * max4Generators.1⁻¹ =
      elementaryGenerator 0 * elementaryGenerator 1 * elementaryGenerator 2 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.1 * modelSubgroup.subtype (elementaryGenerator 1) *
    (modelSubgroup.subtype max4Generators.1)⁻¹ = modelSubgroup.subtype (elementaryGenerator 0) * modelSubgroup.subtype (elementaryGenerator 1) * modelSubgroup.subtype (elementaryGenerator 2)
  simpa only [gen_eq, LocalCardinality.Max4.generator0_eq, elementaryPermutation_eq]
    using first_conj_one_table

private theorem first_conj_two_chunk0 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 0 = true := by
  decide +kernel

private theorem first_conj_two_chunk1 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 1 = true := by
  decide +kernel

private theorem first_conj_two_chunk2 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 2 = true := by
  decide +kernel

private theorem first_conj_two_chunk3 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 3 = true := by
  decide +kernel

private theorem first_conj_two_chunk4 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 4 = true := by
  decide +kernel

private theorem first_conj_two_chunk5 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 5 = true := by
  decide +kernel

private theorem first_conj_two_chunk6 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 6 = true := by
  decide +kernel

private theorem first_conj_two_chunk7 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 7 = true := by
  decide +kernel

private theorem first_conj_two_chunk8 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 8 = true := by
  decide +kernel

private theorem first_conj_two_chunk9 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 9 = true := by
  decide +kernel

private theorem first_conj_two_chunk10 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 10 = true := by
  decide +kernel

private theorem first_conj_two_chunk11 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 11 = true := by
  decide +kernel

private theorem first_conj_two_chunk12 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 12 = true := by
  decide +kernel

private theorem first_conj_two_chunk13 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 13 = true := by
  decide +kernel

private theorem first_conj_two_chunk14 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 14 = true := by
  decide +kernel

private theorem first_conj_two_chunk15 :
    checkChunk (fun x => (gen 0 * elementaryPermutation 2 * (gen 0)⁻¹) x = (elementaryPermutation 2) x) 15 = true := by
  decide +kernel

private theorem first_conj_two_table : gen 0 * elementaryPermutation 2 * (gen 0)⁻¹ = elementaryPermutation 2 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact first_conj_two_chunk0
  · exact first_conj_two_chunk1
  · exact first_conj_two_chunk2
  · exact first_conj_two_chunk3
  · exact first_conj_two_chunk4
  · exact first_conj_two_chunk5
  · exact first_conj_two_chunk6
  · exact first_conj_two_chunk7
  · exact first_conj_two_chunk8
  · exact first_conj_two_chunk9
  · exact first_conj_two_chunk10
  · exact first_conj_two_chunk11
  · exact first_conj_two_chunk12
  · exact first_conj_two_chunk13
  · exact first_conj_two_chunk14
  · exact first_conj_two_chunk15

/-- Conjugation of basis element 2 by max4 generator 1. -/
public theorem first_conj_two :
    max4Generators.1 * elementaryGenerator 2 * max4Generators.1⁻¹ =
      elementaryGenerator 2 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.1 * modelSubgroup.subtype (elementaryGenerator 2) *
    (modelSubgroup.subtype max4Generators.1)⁻¹ = modelSubgroup.subtype (elementaryGenerator 2)
  simpa only [gen_eq, LocalCardinality.Max4.generator0_eq, elementaryPermutation_eq]
    using first_conj_two_table

private theorem second_conj_zero_chunk0 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 0 = true := by
  decide +kernel

private theorem second_conj_zero_chunk1 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 1 = true := by
  decide +kernel

private theorem second_conj_zero_chunk2 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 2 = true := by
  decide +kernel

private theorem second_conj_zero_chunk3 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 3 = true := by
  decide +kernel

private theorem second_conj_zero_chunk4 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 4 = true := by
  decide +kernel

private theorem second_conj_zero_chunk5 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 5 = true := by
  decide +kernel

private theorem second_conj_zero_chunk6 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 6 = true := by
  decide +kernel

private theorem second_conj_zero_chunk7 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 7 = true := by
  decide +kernel

private theorem second_conj_zero_chunk8 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 8 = true := by
  decide +kernel

private theorem second_conj_zero_chunk9 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 9 = true := by
  decide +kernel

private theorem second_conj_zero_chunk10 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 10 = true := by
  decide +kernel

private theorem second_conj_zero_chunk11 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 11 = true := by
  decide +kernel

private theorem second_conj_zero_chunk12 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 12 = true := by
  decide +kernel

private theorem second_conj_zero_chunk13 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 13 = true := by
  decide +kernel

private theorem second_conj_zero_chunk14 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 14 = true := by
  decide +kernel

private theorem second_conj_zero_chunk15 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 0 * (gen 1)⁻¹) x = (elementaryPermutation 0 * elementaryPermutation 1) x) 15 = true := by
  decide +kernel

private theorem second_conj_zero_table : gen 1 * elementaryPermutation 0 * (gen 1)⁻¹ = elementaryPermutation 0 * elementaryPermutation 1 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact second_conj_zero_chunk0
  · exact second_conj_zero_chunk1
  · exact second_conj_zero_chunk2
  · exact second_conj_zero_chunk3
  · exact second_conj_zero_chunk4
  · exact second_conj_zero_chunk5
  · exact second_conj_zero_chunk6
  · exact second_conj_zero_chunk7
  · exact second_conj_zero_chunk8
  · exact second_conj_zero_chunk9
  · exact second_conj_zero_chunk10
  · exact second_conj_zero_chunk11
  · exact second_conj_zero_chunk12
  · exact second_conj_zero_chunk13
  · exact second_conj_zero_chunk14
  · exact second_conj_zero_chunk15

/-- Conjugation of basis element 0 by max4 generator 2. -/
public theorem second_conj_zero :
    max4Generators.2 * elementaryGenerator 0 * max4Generators.2⁻¹ =
      elementaryGenerator 0 * elementaryGenerator 1 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.2 * modelSubgroup.subtype (elementaryGenerator 0) *
    (modelSubgroup.subtype max4Generators.2)⁻¹ = modelSubgroup.subtype (elementaryGenerator 0) * modelSubgroup.subtype (elementaryGenerator 1)
  simpa only [gen_eq, LocalCardinality.Max4.generator1_eq, elementaryPermutation_eq]
    using second_conj_zero_table

private theorem second_conj_one_chunk0 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 0 = true := by
  decide +kernel

private theorem second_conj_one_chunk1 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 1 = true := by
  decide +kernel

private theorem second_conj_one_chunk2 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 2 = true := by
  decide +kernel

private theorem second_conj_one_chunk3 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 3 = true := by
  decide +kernel

private theorem second_conj_one_chunk4 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 4 = true := by
  decide +kernel

private theorem second_conj_one_chunk5 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 5 = true := by
  decide +kernel

private theorem second_conj_one_chunk6 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 6 = true := by
  decide +kernel

private theorem second_conj_one_chunk7 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 7 = true := by
  decide +kernel

private theorem second_conj_one_chunk8 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 8 = true := by
  decide +kernel

private theorem second_conj_one_chunk9 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 9 = true := by
  decide +kernel

private theorem second_conj_one_chunk10 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 10 = true := by
  decide +kernel

private theorem second_conj_one_chunk11 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 11 = true := by
  decide +kernel

private theorem second_conj_one_chunk12 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 12 = true := by
  decide +kernel

private theorem second_conj_one_chunk13 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 13 = true := by
  decide +kernel

private theorem second_conj_one_chunk14 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 14 = true := by
  decide +kernel

private theorem second_conj_one_chunk15 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 1 * (gen 1)⁻¹) x = (elementaryPermutation 1 * elementaryPermutation 2) x) 15 = true := by
  decide +kernel

private theorem second_conj_one_table : gen 1 * elementaryPermutation 1 * (gen 1)⁻¹ = elementaryPermutation 1 * elementaryPermutation 2 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact second_conj_one_chunk0
  · exact second_conj_one_chunk1
  · exact second_conj_one_chunk2
  · exact second_conj_one_chunk3
  · exact second_conj_one_chunk4
  · exact second_conj_one_chunk5
  · exact second_conj_one_chunk6
  · exact second_conj_one_chunk7
  · exact second_conj_one_chunk8
  · exact second_conj_one_chunk9
  · exact second_conj_one_chunk10
  · exact second_conj_one_chunk11
  · exact second_conj_one_chunk12
  · exact second_conj_one_chunk13
  · exact second_conj_one_chunk14
  · exact second_conj_one_chunk15

/-- Conjugation of basis element 1 by max4 generator 2. -/
public theorem second_conj_one :
    max4Generators.2 * elementaryGenerator 1 * max4Generators.2⁻¹ =
      elementaryGenerator 1 * elementaryGenerator 2 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.2 * modelSubgroup.subtype (elementaryGenerator 1) *
    (modelSubgroup.subtype max4Generators.2)⁻¹ = modelSubgroup.subtype (elementaryGenerator 1) * modelSubgroup.subtype (elementaryGenerator 2)
  simpa only [gen_eq, LocalCardinality.Max4.generator1_eq, elementaryPermutation_eq]
    using second_conj_one_table

private theorem second_conj_two_chunk0 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 0 = true := by
  decide +kernel

private theorem second_conj_two_chunk1 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 1 = true := by
  decide +kernel

private theorem second_conj_two_chunk2 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 2 = true := by
  decide +kernel

private theorem second_conj_two_chunk3 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 3 = true := by
  decide +kernel

private theorem second_conj_two_chunk4 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 4 = true := by
  decide +kernel

private theorem second_conj_two_chunk5 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 5 = true := by
  decide +kernel

private theorem second_conj_two_chunk6 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 6 = true := by
  decide +kernel

private theorem second_conj_two_chunk7 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 7 = true := by
  decide +kernel

private theorem second_conj_two_chunk8 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 8 = true := by
  decide +kernel

private theorem second_conj_two_chunk9 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 9 = true := by
  decide +kernel

private theorem second_conj_two_chunk10 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 10 = true := by
  decide +kernel

private theorem second_conj_two_chunk11 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 11 = true := by
  decide +kernel

private theorem second_conj_two_chunk12 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 12 = true := by
  decide +kernel

private theorem second_conj_two_chunk13 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 13 = true := by
  decide +kernel

private theorem second_conj_two_chunk14 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 14 = true := by
  decide +kernel

private theorem second_conj_two_chunk15 :
    checkChunk (fun x => (gen 1 * elementaryPermutation 2 * (gen 1)⁻¹) x = (elementaryPermutation 1) x) 15 = true := by
  decide +kernel

private theorem second_conj_two_table : gen 1 * elementaryPermutation 2 * (gen 1)⁻¹ = elementaryPermutation 1 := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact second_conj_two_chunk0
  · exact second_conj_two_chunk1
  · exact second_conj_two_chunk2
  · exact second_conj_two_chunk3
  · exact second_conj_two_chunk4
  · exact second_conj_two_chunk5
  · exact second_conj_two_chunk6
  · exact second_conj_two_chunk7
  · exact second_conj_two_chunk8
  · exact second_conj_two_chunk9
  · exact second_conj_two_chunk10
  · exact second_conj_two_chunk11
  · exact second_conj_two_chunk12
  · exact second_conj_two_chunk13
  · exact second_conj_two_chunk14
  · exact second_conj_two_chunk15

/-- Conjugation of basis element 2 by max4 generator 2. -/
public theorem second_conj_two :
    max4Generators.2 * elementaryGenerator 2 * max4Generators.2⁻¹ =
      elementaryGenerator 1 := by
  apply Subtype.ext
  change modelSubgroup.subtype max4Generators.2 * modelSubgroup.subtype (elementaryGenerator 2) *
    (modelSubgroup.subtype max4Generators.2)⁻¹ = modelSubgroup.subtype (elementaryGenerator 1)
  simpa only [gen_eq, LocalCardinality.Max4.generator1_eq, elementaryPermutation_eq]
    using second_conj_two_table

private theorem commute_chunk0 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 0 = true := by
  decide +kernel

private theorem commute_chunk1 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 1 = true := by
  decide +kernel

private theorem commute_chunk2 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 2 = true := by
  decide +kernel

private theorem commute_chunk3 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 3 = true := by
  decide +kernel

private theorem commute_chunk4 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 4 = true := by
  decide +kernel

private theorem commute_chunk5 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 5 = true := by
  decide +kernel

private theorem commute_chunk6 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 6 = true := by
  decide +kernel

private theorem commute_chunk7 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 7 = true := by
  decide +kernel

private theorem commute_chunk8 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 8 = true := by
  decide +kernel

private theorem commute_chunk9 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 9 = true := by
  decide +kernel

private theorem commute_chunk10 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 10 = true := by
  decide +kernel

private theorem commute_chunk11 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 11 = true := by
  decide +kernel

private theorem commute_chunk12 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 12 = true := by
  decide +kernel

private theorem commute_chunk13 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 13 = true := by
  decide +kernel

private theorem commute_chunk14 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 14 = true := by
  decide +kernel

private theorem commute_chunk15 :
    checkChunk (fun x => (elementaryPermutation 0 * elementaryPermutation 1) x =
      (elementaryPermutation 1 * elementaryPermutation 0) x) 15 = true := by
  decide +kernel

/-- The first two marked elementary generators commute. -/
public theorem elementary_zero_one_commute :
    elementaryGenerator 0 * elementaryGenerator 1 =
      elementaryGenerator 1 * elementaryGenerator 0 := by
  have h : elementaryPermutation 0 * elementaryPermutation 1 =
      elementaryPermutation 1 * elementaryPermutation 0 := by
    apply Equiv.ext
    apply allFinChunks
    intro b
    fin_cases b
    · exact commute_chunk0
    · exact commute_chunk1
    · exact commute_chunk2
    · exact commute_chunk3
    · exact commute_chunk4
    · exact commute_chunk5
    · exact commute_chunk6
    · exact commute_chunk7
    · exact commute_chunk8
    · exact commute_chunk9
    · exact commute_chunk10
    · exact commute_chunk11
    · exact commute_chunk12
    · exact commute_chunk13
    · exact commute_chunk14
    · exact commute_chunk15
  apply Subtype.ext
  change modelSubgroup.subtype (elementaryGenerator 0) *
    modelSubgroup.subtype (elementaryGenerator 1) =
    modelSubgroup.subtype (elementaryGenerator 1) * modelSubgroup.subtype (elementaryGenerator 0)
  simpa only [elementaryPermutation_eq] using h

/-- The marked plane generator 0 has square one. -/
public theorem elementary_zero_sq : elementaryGenerator 0 * elementaryGenerator 0 = 1 := by
  have h : elementaryPermutation 0 * elementaryPermutation 0 = 1 :=
    inv_mul_cancel (elementaryPermutation 0)
  apply Subtype.ext
  change modelSubgroup.subtype (elementaryGenerator 0) *
    modelSubgroup.subtype (elementaryGenerator 0) = (1 : Equiv.Perm (Fin 4060))
  simpa only [elementaryPermutation_eq] using h

/-- The marked plane generator 1 has square one. -/
public theorem elementary_one_sq : elementaryGenerator 1 * elementaryGenerator 1 = 1 := by
  have h : elementaryPermutation 1 * elementaryPermutation 1 = 1 :=
    inv_mul_cancel (elementaryPermutation 1)
  apply Subtype.ext
  change modelSubgroup.subtype (elementaryGenerator 1) *
    modelSubgroup.subtype (elementaryGenerator 1) = (1 : Equiv.Perm (Fin 4060))
  simpa only [elementaryPermutation_eq] using h

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightAction
