module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection

/-!
# Rank and order obstructions to seven components

Both A₇ and a perfect central three-cover have order divisible by 2520:
for the cover, use its actual central quotient onto A₇. They also have
three-rank at least two. Either obstruction can exclude every embedded
seven-group, and hence every component of a common fixed subgroup for an
arbitrary two-subgroup of automorphisms. No reduction of component membership
from a common fixed subgroup to a single automorphism's fixed subgroup is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the Theorem C
inspection in E.6.18, printed p.252; Theorem C and Remark A.2.4, printed p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
variable {S : Type*} [Group S]

/-- The central-cover case uses quotient divisibility, not an assumed order. -/
theorem seven_card_dvd {L : Subgroup S} (h : IsSeven L) : 2520 ∣ Nat.card L := by
  have ha : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, ha]
  · obtain ⟨_, _, ⟨e⟩⟩ := h
    have hd := (center L).card_quotient_dvd_card
    rwa [Nat.card_congr e.toEquiv, ha] at hd

/-- An order obstruction excludes seven components for the full acting group. -/
theorem inspection_of_not_dvd_card (h : ¬ 2520 ∣ Nat.card S) :
    SevenActionInspection S := by
  intro P _ L _ _ hs
  exact (h ((seven_card_dvd hs).trans L.card_subgroup_dvd_card)).elim

/-- Three-rank at most one excludes both seven models in every subgroup. -/
theorem inspection_of_primeRank_le_one [Finite S] (hr : primeRank 3 S ≤ 1) :
    SevenActionInspection S := by
  intro P _ L _ _ hs
  have hrL := Theory.GroupTheory.primeRank_le_of_injective 3 L.subtype L.subtype_injective
  have hseven := hs.two_le_primeRank
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
