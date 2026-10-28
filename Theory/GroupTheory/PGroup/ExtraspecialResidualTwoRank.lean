module
public import Theory.SpecificGroups.GL2.OddCharacteristicTwoRank
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero

/-!
# Two-rank from an extraspecial residual of order 27

The automorphism action on the central quotient of an extraspecial group of
order 27 has an odd inner kernel and target of two-rank at most two. If this
group is the actual two-residual of an ambient group with trivial two-core,
its centralizer is contained in it, so ambient conjugation also has odd kernel.
The two-rank bound therefore holds on the original ambient group.

Source application: Aschbacher–Smith 15.1.7(7) and15.1.13, p.1091.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace IsExtraspecial
variable {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]

theorem automorphism_twoRank_le_two_of_card_twenty_seven (hP : Nat.card P = 27) :
    primeRank 2 (MulAut P) ≤ 2 := by
  let Z := center P
  let : IsElementaryAbelian 3 (P ⧸ Z) := IsExtraspecial.quotient_elementary_abelian 3 P
  have hQ : Nat.card (P ⧸ Z) = 3 ^ 2 := by
    have hh := Z.card_eq_card_quotient_mul_card_subgroup
    rw [IsExtraspecial.center_order_p 3 P,hP] at hh
    omega
  let f := quotientAut Z
  have hk : primeRank 2 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    change ¬2 ∣ Nat.card (quotientAut (center P)).ker
    rw [quotientAut_center_ker_eq_range_conj (p := 3)]
    have ho : Odd (Nat.card P) := by rw [hP]; decide
    exact (ho.of_dvd_nat (Subgroup.card_range_dvd (MulAut.conj : P →* MulAut P))).not_two_dvd_nat
  have hq := IsElementaryAbelian.automorphism_twoRank_le_two_of_odd_plane
    (p := 3) (by decide) hQ
  have hh := primeRank_le_ker_add (p := 2) f
  rw [hk,zero_add] at hh
  exact hh.trans hq
end IsExtraspecial

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem twoRank_le_two_of_extraspecial_twoResidual
    (hcore : pCore 2 G = ⊥)
    [IsExtraspecial 3 (pResidual 2 G)]
    (hP : Nat.card (pResidual 2 G) = 27) : primeRank 2 G ≤ 2 := by
  let P := pResidual 2 G
  let f : G →* MulAut P := MulAut.conjNormal
  have hk : primeRank 2 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    have ho : Odd (Nat.card P) := by rw [hP]; decide
    have hkle : f.ker ≤ P := by
      rw [MulAut.conjNormal_ker_eq_centralizer]
      exact centralizer_pResidual_le_of_pCore_eq_bot hcore
    exact (ho.of_dvd_nat (card_dvd_of_le hkle)).not_two_dvd_nat
  have hq := IsExtraspecial.automorphism_twoRank_le_two_of_card_twenty_seven hP
  have hh := primeRank_le_ker_add (p := 2) f
  rw [hk,zero_add] at hh
  exact hh.trans hq
end Theory.GroupTheory
