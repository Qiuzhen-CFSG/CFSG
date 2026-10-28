module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels

/-!
# Sylow intersections for the concrete local models

An actor four-group already has the full two-part of a dihedral group of
order four times an odd prime. Likewise a subgroup of order eight has the
full two-part of S₄. Maximality of these local Sylow subgroups proves the
required statement about the literal intersection with the ambient Sylow.
Neither argument requires the ambient Sylow to lie in the local group.

Source: the E0 condition in Aschbacher--Smith, E.1.2, printed p.210.
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner

variable {G : Type*} [Group G]

private theorem intersection_sylow_of_card
    (T : Sylow 2 G) (P H : Subgroup G)
    (hPT : P ≤ (T : Subgroup G)) (hPH : P ≤ H)
    {n r : ℕ} (hP : Nat.card P = 2 ^ n) (hH : Nat.card H = 2 ^ n * r)
    (hr : Odd r) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H := by
  let PH := P.subgroupOf H
  have hPHc : Nat.card PH = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).trans hP
  have hindex : PH.index = r := by
    have he := PH.card_mul_index
    rw [hPHc, hH] at he
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) n) he
  let S : Sylow 2 H := (IsPGroup.of_card hPHc).toSylow (by
    rw [hindex]
    exact hr.not_two_dvd_nat)
  refine ⟨S, (S.is_maximal' (T.isPGroup'.comap_subtype) ?_).symm⟩
  exact fun x hx => hPT hx

/-- A dihedral local model containing the actor automatically has the
literal ambient Sylow intersection required by E0. -/
theorem sylow_intersection_dihedral (T : Sylow 2 G)
    (A H : Subgroup G) (hAT : A ≤ (T : Subgroup G)) (hAH : A ≤ H)
    (hA : IsKleinFour A) {r : ℕ} (hr : Odd r)
    (e : H ≃* DihedralGroup (2 * r)) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H := by
  have hc : Nat.card H = 2 ^ 2 * r := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    ring
  exact intersection_sylow_of_card T A H hAT hAH hA.card_four hc hr

/-- An order-eight subgroup in both T and an S₄ model proves the literal
Sylow intersection, even when T itself has larger order. -/
theorem sylow_intersection_symmetric_four (T : Sylow 2 G)
    (D H : Subgroup G) (hDT : D ≤ (T : Subgroup G)) (hDH : D ≤ H)
    (hD : Nat.card D = 8) (e : H ≃* Equiv.Perm (Fin 4)) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H := by
  have hc : Nat.card H = 2 ^ 3 * 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  exact intersection_sylow_of_card T D H hDT hDH hD hc (by decide)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
