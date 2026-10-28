module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.GroupTheory.PrimeRankZero

/-!
# Positive three-rank in the complete B.4.2 action list

Opposite transvections give cubic elements in every linear row. The actual
derived Sp₄ and G₂ carriers contain the checked binary cubic witnesses;
permutation cycles handle alternating rows, and the triple cover has cubic
center. Transport uses the marked component isomorphism in each source row.
In particular, the small derived groups are not replaced by the full groups.

The section-image corollary applies to B.5.5's actual chief action. Constructing
that faithful chief section from B.5.3 remains the B.5.5 source implication.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.4.2, p.86,
and B.5.5(1iii–iv), pp.104–105.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
open QuasisimpleSource

private theorem rank_pos_of_three_dvd {D : Type*} [Group D] [Finite D]
    (h : 3 ∣ Nat.card D) : 0 < primeRank 3 D :=
  Nat.pos_of_ne_zero (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he h)

private theorem linear_rank_pos (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) :
    0 < primeRank 3 (Matrix.SpecialLinearGroup (Fin d) F.Carrier) := by
  have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F.Carrier) (i := (⟨0, by omega⟩ : Fin d)) (j := (⟨1, by omega⟩ : Fin d)) (by
      exact Fin.ne_of_val_ne (by change (0 : ℕ) ≠ 1; decide))
  apply rank_pos_of_three_dvd
  exact (h3.trans (card_subgroup_dvd_card _)).trans
    (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center
      (Matrix.SpecialLinearGroup (Fin d) F.Carrier)))
      (QuotientGroup.mk'_surjective _))

private theorem alternating_rank_pos {n : ℕ} (hn : n = 5 ∨ 6 ≤ n) :
    0 < primeRank 3 (alternatingGroup (Fin n)) := by
  rcases hn with rfl | hn
  · apply rank_pos_of_three_dvd
    rw [nat_card_alternatingGroup]
    norm_num
  · exact lt_of_lt_of_le (by decide : 0 < 2)
      (alternatingGroup.TwoThreeCycles.two_le_primeRank hn)

/-- Every row of the complete B.4.2 list has positive three-rank on its
specified component, including both small derived endpoints. -/
theorem action_case_rank_pos
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {L H : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ L H) : 0 < primeRank 3 L := by
  cases h with
  | linearTwo F _ e _ _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_rank_pos F (by decide)
  | linearThree F _ e _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_rank_pos F (by decide)
  | symplectic F _ _ e _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact lt_of_lt_of_le (by decide : 0 < 2)
        (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
          (primeRank_le_of_injective 3 _ (commutator _).subtype_injective))
  | symplecticTwo e _ =>
      rw [primeRank_equiv 3 e.subgroupEquiv]
      exact lt_of_lt_of_le (by decide : 0 < 2)
        Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
  | g2 F _ _ e _ _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact lt_of_lt_of_le (by decide : 0 < 2)
        (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
          (primeRank_le_of_injective 3 _ (commutator _).subtype_injective))
  | g2Two e _ _ =>
      rw [primeRank_equiv 3 e.subgroupEquiv]
      exact lt_of_lt_of_le (by decide : 0 < 2)
        Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  | symmetric n hn e _ _ =>
      rw [primeRank_equiv 3 e.subgroupEquiv]
      exact alternating_rank_pos (by omega)
  | alternatingSix _ e _ _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact alternating_rank_pos (Or.inr (by decide))
  | alternatingSeven _ _ e _ _ _ =>
      rw [primeRank_equiv 3 e]
      exact alternating_rank_pos (Or.inr (by decide))
  | tripleSix _ a _ =>
      apply rank_pos_of_three_dvd
      have hcard : Nat.card (center L) = 3 := by
        rw [Nat.card_congr a.centerEquiv.toEquiv]
        simp
      exact hcard ▸ card_subgroup_dvd_card (center L)
  | binaryLinear d hd _ e _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_rank_pos BinaryField.two (by omega)
  | orthogonalSix _ _ e _ _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact alternating_rank_pos (Or.inr (by decide))
  | symmetricEight _ e _ =>
      rw [primeRank_equiv 3 e.subgroupEquiv]
      exact alternating_rank_pos (Or.inr (by decide))
  | exteriorFive _ _ e _ _ _ =>
      rw [primeRank_equiv 3 e]
      exact linear_rank_pos BinaryField.two (by decide)

/-- The actual image of a component on a section has positive three-rank in
every source row, so its original preimage does too. Surjectivity onto the
literal image suffices; no central-quotient rank equality is assumed. -/
theorem rank_pos_of_section_action
    {G D V : Type*} [Group G] [Finite G] [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (f : G →* D) (L : Subgroup G) {ρ : Representation (ZMod 2) D V}
    {H : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ (L.map f) H) :
    0 < primeRank 3 L := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hi := PrimeRank.eq_zero_of_surjective (f.subgroupMap L)
    (f.subgroupMap_surjective L) hz
  exact (Nat.ne_of_gt (action_case_rank_pos h)) hi

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
