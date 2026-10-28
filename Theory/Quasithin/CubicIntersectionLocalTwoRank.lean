module
public import Theory.GroupTheory.CubicIntersectionRankLower
public import Theory.Quasithin.LocalRank
/-!
# Local rank two in a product with cubic intersection

A two-local of rank at least two in one factor and an ordinary rank-two
subgroup in a commuting factor generate rank at least three inside the
same actual ambient two-local, when their intersection has order at most
three. The original normalizer and embedded two-subgroup remain explicit.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.Quasithin.CubicIntersection
variable {H : Type*} [Group H] [Finite H]
theorem not_quasithin_of_local_two_ordinary_two
    (A B : Subgroup H) (hc : A ≤ centralizer (B : Set H))
    (hI : Nat.card (A ⊓ B : Subgroup H) ≤ 3)
    (hA : 2 ≤ twoLocalPrimeRank 3 A) (hB : 2 ≤ primeRank 3 B) :
    ¬ IsQuasithin H := by
  intro hH
  have hex : ∃ M : Subgroup A, IsTwoLocal M ∧ 2 ≤ primeRank 3 M := by
    by_contra! hn
    have hsmall : twoLocalPrimeRank 3 A ≤ 1 :=
      (twoLocalPrimeRank_le_iff 3 1).mpr (fun M hM => by have := hn M hM; omega)
    omega
  obtain ⟨M, ⟨Q, hQne, hQ, rfl⟩, hM⟩ := hex
  let R := Q.map A.subtype
  let N := normalizer (R : Set H)
  let L := (normalizer (Q : Set A)).map A.subtype
  have hLA : L ≤ A := map_subtype_le _
  have hRA : R ≤ A := map_subtype_le _
  have hLN : L ≤ N := le_normalizer_map A.subtype
  have hBN : B ≤ N := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro y hy x hx
    exact (hc (hRA hx) y hy).symm
  have hcN : L.subgroupOf N ≤ centralizer (B.subgroupOf N : Set N) := by
    intro x hx y hy
    exact Subtype.ext (hc (hLA hx) y hy)
  have hiN : Nat.card (L.subgroupOf N ⊓ B.subgroupOf N : Subgroup N) ≤ 3 := by
    change Nat.card ((L ⊓ B).subgroupOf N) ≤ 3
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hLN)).toEquiv]
    exact (card_le_of_le (inf_le_inf hLA le_rfl)).trans hI
  have hLNrank : 2 ≤ primeRank 3 (L.subgroupOf N) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hLN)]
    rw [← primeRank_equiv 3
      ((normalizer (Q : Set A)).equivMapOfInjective A.subtype A.subtype_injective)]
    exact hM
  have hBNrank : 2 ≤ primeRank 3 (B.subgroupOf N) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hBN)]
    exact hB
  have hbig := three_le_primeRank_of_cubic_intersection
    (L.subgroupOf N) (B.subgroupOf N) hcN hiN hLNrank hBNrank
  have hRne : R ≠ ⊥ := fun hh => hQne
    ((map_eq_bot_iff_of_injective Q A.subtype_injective).mp hh)
  have hsmall := isQuasithin_iff_twoLocal.mp hH N
    ⟨R, hRne, hQ.map A.subtype, rfl⟩ 3 Nat.prime_three (by decide)
  omega
end Theory.Quasithin.CubicIntersection
