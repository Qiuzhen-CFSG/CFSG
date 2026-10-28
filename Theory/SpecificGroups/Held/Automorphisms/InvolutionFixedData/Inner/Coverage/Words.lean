module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.Reduction
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.FinCases

/-!
# Checked permutation expressions for the Held binary words

The ten factors of the published binary enumeration are precisely the reverse
of the two-group certificate's ascending sequence. Their existing checked
permutation tables therefore evaluate each normal form in the actual Held
representation. This comparison does not assume that the words exhaust the
representative, nor does it import the legacy normalizer catalogue.

Source: the ATLAS HeG1-p2058B0 carrier and the retained polycyclic word data in
`LocalPairs/SylowGeometry/Calculations/TwoGroup/Source/`; GLS3 Table 5.3p.
-/

namespace Held.InvolutionFixedData.Coverage
open LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup
open TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-- The binary enumeration and the certified two-series use reverse order. -/
public theorem word_eq_pcGenerator (i : Fin 10) :
    (word (pcWord i)).val = pcGenerator ⟨9 - i.val, by omega⟩ := by
  fin_cases i <;>
    simp [word, letter, pcWord, pcGenerator, mul_assoc] <;> rfl

/-- A computable expression using the ten already checked permutation tables. -/
@[expose] public def normalPerm (n : Fin 1024) : Equiv.Perm (Fin 2058) :=
  ((List.finRange 10).map (fun i => Tables.pcTable ⟨9 - i.val, by omega⟩ ^
    (n.val / 2 ^ i.val % 2))).prod

/-- The table expression is the image of the literal word, in the same factor order. -/
public theorem normalForm_representation (n : Fin 1024) :
    representation (normalForm n).val = normalPerm n := by
  change (representation.comp representative.subtype) (normalForm n) = normalPerm n
  simp only [normalForm, normalPerm, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, map_pow]
  apply congrArg (· ^ (n.val / 2 ^ i.val % 2))
  change representation (word (pcWord i)).val = _
  rw [word_eq_pcGenerator, Tables.pcTable_eq]

/-- The zero bit string evaluates to the identity. -/
public theorem normalForm_zero : (normalForm 0).val = 1 := by
  change (1 : He) = 1
  rfl

end Held.InvolutionFixedData.Coverage
