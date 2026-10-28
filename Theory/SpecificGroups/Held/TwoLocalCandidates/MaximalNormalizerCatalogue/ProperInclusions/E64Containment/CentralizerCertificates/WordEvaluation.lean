module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.FinCases

/-!
# Table evaluation of the Held catalogue words

Evaluate signed words in the four already certified permutation tables, then
transport through the faithful representation. This avoids expanding each
representative generator back into its long original ATLAS word in every check.
The tables and their inverse laws have been checked by the Lean kernel.

Source: ATLAS HeG1-p2058B0 and HeG1-max3W1; the unchanged words and certified
lookup permutations in `Calculations.TwoGroup.Tables`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open LocalPairs.SylowGeometry.Calculations

private def fastGenerator : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => TwoGroup.Tables.g0
  | 1 => TwoGroup.Tables.g1
  | 2 => TwoGroup.Tables.g2
  | _ => TwoGroup.Tables.g3
private theorem fastGenerator_eq (i : Fin 4) :
    fastGenerator i = representation (generator i) := by
  fin_cases i
  · exact TwoGroup.Tables.g0_eq
  · exact TwoGroup.Tables.g1_eq
  · exact TwoGroup.Tables.g2_eq
  · exact TwoGroup.Tables.g3_eq
private def fastLetter (k : ℤ) : Equiv.Perm (Fin 2058) :=
  let x := fastGenerator (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then x⁻¹ else x
private theorem fastLetter_eq (k : ℤ) : fastLetter k = representation (letter k : He) := by
  by_cases hk : k < 0 <;>
    simp only [fastLetter, letter, hk, if_true, if_false, fastGenerator_eq,
      Subgroup.coe_inv, map_inv]
/-- Evaluate a catalogue word using the certified generator lookup tables. -/
@[expose] public def fastWord (w : List ℤ) : Equiv.Perm (Fin 2058) :=
  (w.map (fun k =>
    let x : Equiv.Perm (Fin 2058) := match Fin.ofNat 4 (k.natAbs - 1) with
      | 0 => TwoGroup.Tables.g0
      | 1 => TwoGroup.Tables.g1
      | 2 => TwoGroup.Tables.g2
      | _ => TwoGroup.Tables.g3
    if k < 0 then x⁻¹ else x)).prod

/-- Table evaluation agrees with the action of the unchanged literal word. -/
public theorem fastWord_eq (w : List ℤ) : fastWord w = representation (word w : He) := by
  change _ = (representation.comp representative.subtype) ((w.map letter).prod)
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _
  exact fastLetter_eq k


end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
