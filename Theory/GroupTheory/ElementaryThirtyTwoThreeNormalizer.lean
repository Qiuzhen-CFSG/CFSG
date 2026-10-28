module

public import Theory.GroupTheory.ElementaryThirtyTwoThreeSubgroups
public import Theory.GroupTheory.ElementarySixteenThreeNormalizer
public import Theory.GroupAction.CoprimeNormalizerDecomposition

/-!
# Three-subgroup normalizers on an elementary thirty-two

An order-three automorphism subgroup has a fixed subgroup of order two or eight.
Coprime splitting bounds its normalizer by the automorphism group of the fixed
summand and the restricted normalizer on the commutator summand. When the fixed
summand has order two, its automorphism group is trivial and the order-sixteen
normalizer bound applies. Otherwise the two summands have orders eight and four,
so the normalizer order divides 168 * 6. In either case, 64 cannot divide it.

Source: Parrott, A Characterization of the Tits' Simple Group (1972),
printed p.673, property (4). No classification assumptions are used.
-/

open Subgroup
open scoped IsMulCommutative

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

/-- Sixty-four does not divide the order of the normalizer of an order-three
subgroup of the automorphism group of an elementary abelian thirty-two. -/
public theorem not_sixtyfour_dvd_card_normalizer_of_elementary_thirtytwo_three
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 3) :
    ¬ 64 ∣ Nat.card (normalizer (A : Set (MulAut E))) := by
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by rw [hA, hE]; decide
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := E) (A := A) (Group.isSolvable_of_comm (fun a b : E => mul_comm a b))
      hcop inferInstance
  have hprod : Nat.card (FixedPoints.subgroup A E) *
      Nat.card (commutatorAction A E) = 32 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (FixedPoints.subgroup A E)
      (commutatorAction A E) (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top, card_top, hE] at hh
    exact hh.symm
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  rcases fixed_card_two_or_eight_of_elementary_thirtytwo_three hE A hA with hF | hF
  · have hC : Nat.card (commutatorAction A E) = 16 := by rw [hF] at hprod; omega
    have hAut : Nat.card (MulAut (FixedPoints.subgroup A E)) = 1 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 1 (by simpa using hF)]
      decide
    rw [hAut, one_mul] at hdiv
    exact fun h => not_sixtyfour_dvd_card_normalizer_of_elementary_sixteen_three
      hC D (hD.trans hA) (h.trans hdiv)
  · have hC : Nat.card (commutatorAction A E) = 4 := by rw [hF] at hprod; omega
    have hAutF : Nat.card (MulAut (FixedPoints.subgroup A E)) = 168 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 3 (by simpa using hF)]
      decide
    have hAutC : Nat.card (MulAut (commutatorAction A E)) = 6 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hC)]
      decide
    have hnorm : Nat.card (normalizer (D : Set (MulAut (commutatorAction A E)))) ∣ 6 :=
      hAutC ▸ (normalizer (D : Set (MulAut (commutatorAction A E)))).card_subgroup_dvd_card
    rw [hAutF] at hdiv
    intro h
    have hh : 64 ∣ 168 * 6 := (h.trans hdiv).trans (Nat.mul_dvd_mul_left 168 hnorm)
    norm_num at hh
