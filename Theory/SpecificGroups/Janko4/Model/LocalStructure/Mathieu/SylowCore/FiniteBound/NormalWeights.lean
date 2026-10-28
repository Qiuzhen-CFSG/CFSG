module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Coverage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.ZeroWeights
import Mathlib.Tactic.FinCases

/-!
# Normality-based fixed-mask weights for the literal Sylow candidate

An elementary subgroup contains only square-one elements, and its elements
commute with all their conjugates by the ambient Sylow candidate. The checked
zero-weight witnesses therefore exclude every zero entry of `weight`.

For each positive nonidentity entry, a checked conjugation puts one of 22
representatives in the normal subgroup. For those representatives, short lists
of conjugates yield the exact cached row equations. Their kernel-checked
finite counts bound the subgroup's common fixed masks. The identity case is
the inclusion into `Fin 2048`.

Source data: the ATLAS max1 Sylow words in `QuotientInvolutions.SylowData`,
and the marked row action in `Image.StarData` and `FixedCoordinates`.
`NormalWeights/source` explains discovery and the separate kernel obligations.
-/

public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Simplicity.Max1Fusion.QuotientInvolutions
open NormalWeights

private theorem representative_bound (B : Subgroup sylowCandidate) (hn : B.Normal)
    (k : Fin 22) (hk : element (representatives k) ∈ B) :
    Nat.card (FixedMasks B) ≤ bounds k := by
  fin_cases k
  · exact card_le_conjugate_rows B hn (representatives 0) hk conjugates0
      conjugates0_valid cachedRows0 cachedRows0_valid (bounds 0) cachedRows0_count
  · exact card_le_conjugate_rows B hn (representatives 1) hk conjugates1
      conjugates1_valid cachedRows1 cachedRows1_valid (bounds 1) cachedRows1_count
  · exact card_le_conjugate_rows B hn (representatives 2) hk conjugates2
      conjugates2_valid cachedRows2 cachedRows2_valid (bounds 2) cachedRows2_count
  · exact card_le_conjugate_rows B hn (representatives 3) hk conjugates3
      conjugates3_valid cachedRows3 cachedRows3_valid (bounds 3) cachedRows3_count
  · exact card_le_conjugate_rows B hn (representatives 4) hk conjugates4
      conjugates4_valid cachedRows4 cachedRows4_valid (bounds 4) cachedRows4_count
  · exact card_le_conjugate_rows B hn (representatives 5) hk conjugates5
      conjugates5_valid cachedRows5 cachedRows5_valid (bounds 5) cachedRows5_count
  · exact card_le_conjugate_rows B hn (representatives 6) hk conjugates6
      conjugates6_valid cachedRows6 cachedRows6_valid (bounds 6) cachedRows6_count
  · exact card_le_conjugate_rows B hn (representatives 7) hk conjugates7
      conjugates7_valid cachedRows7 cachedRows7_valid (bounds 7) cachedRows7_count
  · exact card_le_conjugate_rows B hn (representatives 8) hk conjugates8
      conjugates8_valid cachedRows8 cachedRows8_valid (bounds 8) cachedRows8_count
  · exact card_le_conjugate_rows B hn (representatives 9) hk conjugates9
      conjugates9_valid cachedRows9 cachedRows9_valid (bounds 9) cachedRows9_count
  · exact card_le_conjugate_rows B hn (representatives 10) hk conjugates10
      conjugates10_valid cachedRows10 cachedRows10_valid (bounds 10) cachedRows10_count
  · exact card_le_conjugate_rows B hn (representatives 11) hk conjugates11
      conjugates11_valid cachedRows11 cachedRows11_valid (bounds 11) cachedRows11_count
  · exact card_le_conjugate_rows B hn (representatives 12) hk conjugates12
      conjugates12_valid cachedRows12 cachedRows12_valid (bounds 12) cachedRows12_count
  · exact card_le_conjugate_rows B hn (representatives 13) hk conjugates13
      conjugates13_valid cachedRows13 cachedRows13_valid (bounds 13) cachedRows13_count
  · exact card_le_conjugate_rows B hn (representatives 14) hk conjugates14
      conjugates14_valid cachedRows14 cachedRows14_valid (bounds 14) cachedRows14_count
  · exact card_le_conjugate_rows B hn (representatives 15) hk conjugates15
      conjugates15_valid cachedRows15 cachedRows15_valid (bounds 15) cachedRows15_count
  · exact card_le_conjugate_rows B hn (representatives 16) hk conjugates16
      conjugates16_valid cachedRows16 cachedRows16_valid (bounds 16) cachedRows16_count
  · exact card_le_conjugate_rows B hn (representatives 17) hk conjugates17
      conjugates17_valid cachedRows17 cachedRows17_valid (bounds 17) cachedRows17_count
  · exact card_le_conjugate_rows B hn (representatives 18) hk conjugates18
      conjugates18_valid cachedRows18 cachedRows18_valid (bounds 18) cachedRows18_count
  · exact card_le_conjugate_rows B hn (representatives 19) hk conjugates19
      conjugates19_valid cachedRows19 cachedRows19_valid (bounds 19) cachedRows19_count
  · exact card_le_conjugate_rows B hn (representatives 20) hk conjugates20
      conjugates20_valid cachedRows20 cachedRows20_valid (bounds 20) cachedRows20_count
  · exact card_le_conjugate_rows B hn (representatives 21) hk conjugates21
      conjugates21_valid cachedRows21 cachedRows21_valid (bounds 21) cachedRows21_count

/-- Every entry of the candidate table is a valid bound for the exact row action
of every normal elementary subgroup containing the corresponding element. -/
theorem normalFixedCertificate : NormalFixedCertificate := by
  intro B hn he i hi
  let : IsElementaryAbelian 2 B := he
  rcases positiveTest i (weight_pos_of_mem B hn i hi) with hid | ⟨hc, hw⟩
  · subst i
    have h := Nat.card_le_card_of_injective
      (fun m : FixedMasks B => m.val) Subtype.val_injective
    simpa only [Nat.card_fin, weight_identityIndex] using h
  · rw [hw]
    exact representative_bound B hn (transport i).2
      (mem_of_conjugates B hn i _ _ hi hc)

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
