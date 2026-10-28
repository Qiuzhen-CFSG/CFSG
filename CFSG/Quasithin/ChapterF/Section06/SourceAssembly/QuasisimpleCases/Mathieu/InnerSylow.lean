module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerSquare
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates

/-!
# The literal common Sylow extension in the Mathieu row

The already identified normal C₄² radical lies in the actual common Sylow.
The checked 64-word coordinates put every square in that same radical.
Its quotient has order four and exponent two, so it is E₄. The finite table
records only the two exponents expressing each square in the existing roots;
all equalities are checked by the kernel against the original permutations.

Source: Aschbacher–Smith, F.6.18(12), printed p.310, with 14.2.21's marking.
-/

public noncomputable section
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
open Sporadic.Mathieu.M12SmallPair.SecondSquareControl
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.InnerSquare

abbrev E4 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private def squareCoordinates : Fin 64 → Fin 4 × Fin 4 :=
  ![(0, 0), (2, 0), (2, 0), (1, 0), (0, 0), (0, 0), (0, 2), (0, 0), (2, 2), (0, 0), (2, 0), (2, 0), (2, 0), (1, 0), (3, 2), (1, 0), (3, 2), (0, 0), (1, 2), (3, 0), (2, 0), (1, 2), (0, 0), (2, 0), (3, 0), (0, 0), (0, 2), (0, 0), (2, 2), (0, 0), (2, 0), (0, 0), (2, 2), (0, 0), (0, 0), (0, 0), (0, 0), (2, 2), (0, 2), (0, 0), (0, 0), (0, 0), (0, 0), (0, 2), (3, 2), (1, 0), (3, 2), (0, 0), (1, 2), (1, 2), (0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (3, 0), (2, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (2, 0), (2, 0)]

private theorem square_check : ∀ i : Fin 64,
    (SylowAutomorphismGroup.element i : M12) ^ 2 =
      rootOne ^ (squareCoordinates i).1.val * rootTwo ^ (squareCoordinates i).2.val := by
  decide +kernel

/-- Every square of the actual common Sylow lies in the marked normal radical. -/
theorem sylow_square_mem_radical (x : sylowCandidate) : (x : M12) ^ 2 ∈ radical := by
  obtain ⟨i, rfl⟩ := SylowAutomorphismGroup.element_surjective x
  exact (mem_radical_iff _).mpr
    ⟨(squareCoordinates i).1, (squareCoordinates i).2, (square_check i).symm⟩

@[expose] def sylowRadical : Subgroup sylowCandidate := radical.subgroupOf sylowCandidate

instance : sylowRadical.Normal := by
  apply (normal_subgroupOf_iff_le_normalizer radical_le_sylow).mpr
  exact inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer
    (radical_le_sylow.trans inf_le_right)).mp SecondSquareControl.radical_normal)

def sylowRadicalEquiv : sylowRadical ≃* C4Square :=
  (subgroupOfEquivOfLe radical_le_sylow).trans radicalEquiv

private theorem sylowRadical_card : Nat.card sylowRadical = 16 := by
  change Nat.card (radical.subgroupOf sylowCandidate) = 16
  rw [Nat.card_congr (subgroupOfEquivOfLe radical_le_sylow).toEquiv]
  exact radical_card

private theorem sylowQuotient_card : Nat.card (sylowCandidate ⧸ sylowRadical) = 4 := by
  have h := sylowRadical.card_mul_index
  rw [sylowRadical_card, card_sylowCandidate] at h
  change sylowRadical.index = 4
  omega

private theorem sylowQuotient_square (x : sylowCandidate ⧸ sylowRadical) : x ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective sylowRadical x
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact sylow_square_mem_radical g

/-- The actual quotient of the common Sylow by the C₄² radical is E₄. -/
def sylowQuotientEquiv : (sylowCandidate ⧸ sylowRadical) ≃* E4 := by
  let Q := sylowCandidate ⧸ sylowRadical
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (sylowCandidate ⧸ sylowRadical)
    rw [sylowQuotient_card]
    decide)
  let : IsKleinFour Q := {
    card_four := sylowQuotient_card
    exponent_two := by
      apply Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one sylowQuotient_square)
      obtain ⟨x, hx⟩ := exists_ne (1 : Q)
      have ho : orderOf x = 2 := orderOf_eq_prime (sylowQuotient_square x) hx
      simpa only [ho] using Monoid.order_dvd_exponent x }
  let : IsKleinFour E4 := {
    card_four := by simp [E4, Nat.card_eq_fintype_card]
    exponent_two := by simp [E4, Monoid.exponent_prod] }
  exact Classical.choice IsKleinFour.nonempty_mulEquiv

/-- The full common-Sylow extension assertion used in F.6.18(12). -/
theorem sylow_extension : ∃ N : Subgroup sylowCandidate, ∃ _ : N.Normal,
    Nonempty (N ≃* C4Square) ∧ Nonempty ((sylowCandidate ⧸ N) ≃* E4) :=
  ⟨sylowRadical, inferInstance, ⟨sylowRadicalEquiv⟩, ⟨sylowQuotientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.InnerSquare
