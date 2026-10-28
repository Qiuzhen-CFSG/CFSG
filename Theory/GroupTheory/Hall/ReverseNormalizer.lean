module
public import Theory.GroupTheory.Hall.TwoResidual
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Reverse normalization from an odd Hall intersection

If B normalizes an odd subgroup C, the product CB has odd order. Suppose
C normalizes R, B lies in R, and CB ∩ R lies in a group A in which B is
Hall. Hall maximality gives CB ∩ R = B, so C normalizes B.

This is the subgroup step in Aschbacher–Smith 10.2.3, printed p.746,
with R the embedded two-residual of the original H-star group.
-/

public section
open Subgroup
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

/-- An invariant odd torus reverses normalization when it normalizes a
subgroup whose intersection with the product has the original odd Hall. -/
theorem reverse_normalizes_of_normalizes_intersection
    (A B C R : Subgroup G) (hBA : B ≤ A)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf A))
    (hC : Odd (Nat.card C)) (hBC : B ≤ normalizer (C : Set G))
    (hBR : B ≤ R) (hCR : C ≤ normalizer (R : Set G))
    (hinter : (C ⊔ B) ⊓ R ≤ A) : C ≤ normalizer (B : Set G) := by
  let E := (C ⊔ B) ⊓ R
  have hBE : B ≤ E := le_inf le_sup_right hBR
  have hoB : Odd (Nat.card B) := by
    have hh := odd_hall_odd hB
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hh
  have hoCB : Odd (Nat.card (C ⊔ B : Subgroup G)) := by
    have hh := hC.mul hoB
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBC] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hoE : Odd (Nat.card (E.subgroupOf A)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hinter).toEquiv]
    exact hoCB.of_dvd_nat (card_dvd_of_le (show E ≤ C ⊔ B from inf_le_left))
  have hBEA : B.subgroupOf A ≤ E.subgroupOf A := subgroupOf_mono A hBE
  have hHallE : IsHallSubgroup oddPrimes (E.subgroupOf A) := by
    refine ⟨?_,?_⟩
    · intro p hp he
      change p.val = 2 at he
      rw [he] at hp
      exact (Nat.not_even_iff_odd.mpr hoE) (even_iff_two_dvd.mpr hp)
    · intro p hp
      exact hB.p_in_pi_of_p_dvd_index p (hp.trans (index_dvd_of_le hBEA))
  have hEq : B = E := by
    have hh := congrArg (fun K : Subgroup A => K.map A.subtype)
      (hB.eq_of_le hHallE hBEA)
    rw [map_subgroupOf_eq_of_le hBA,
      map_subgroupOf_eq_of_le (show E ≤ A from hinter)] at hh
    exact hh
  rw [hEq]
  exact (le_inf (le_sup_left.trans (C ⊔ B).le_normalizer) hCR).trans
    inf_normalizer_le_normalizer_inf

end Subgroup.OddHall
