module
public import Theory.GroupTheory.SolvableSemidihedralInvolution
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.Hall.TwoClosedNormal

/-!
# A cyclic odd Hall subgroup fixes the semidihedral central involution

In a solvable finite group with a cyclic odd Hall subgroup, the odd core
is cyclic. If the two-core vanished, Fitting self-centralization would
place the derived group in that odd core, forcing every two-subgroup to
be abelian. Thus a semidihedral Sylow subgroup forces a nontrivial two-core.
Its unique normal elementary subgroup identifies the characteristic
central involution, which is fixed by every automorphism.

Source application: Aschbacher--Smith 5.1.13, printed p.636, the unitary
three-dimensional containing row. The argument is intrinsic finite-group
and Hall theory and does not require a bound on the odd Hall order.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Semidihedral
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normal_le_hall (D N : Subgroup G) [N.Normal]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hN : Odd (Nat.card N)) : N ≤ D := by
  have hcop : Nat.Coprime (Nat.card N) D.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpD
    have hp2 : p = 2 := Classical.not_not.mp
      (hD.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpD)
    exact hN.not_two_dvd_nat (hp2 ▸ hpN)
  have hd : D.relIndex N ∣ D.index := by
    rw [←relIndex_sup_of_normalizes N D le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  exact relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card D N) hd)

private theorem twoCore_ne_bot_of_cyclic_odd_hall
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hna : ¬ IsMulCommutative P) :
    pCore 2 G ≠ ⊥ := by
  intro htwo
  have hOD : pPrimeCore 2 G ≤ D := odd_normal_le_hall D _ hD
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : IsCyclic (pPrimeCore 2 G) :=
    isCyclic_of_injective (inclusion hOD) (inclusion_injective hOD)
  have hd : _root_.commutator G ≤ pPrimeCore 2 G :=
    (commutator_le_centralizer_of_isCyclic_normal (pPrimeCore 2 G)).trans
      (centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs htwo)
  have hc : ⁅P,P⁆ ≤ pPrimeCore 2 G :=
    (commutator_mono (show P ≤ ⊤ from le_top) le_top).trans hd
  have hdis : Disjoint P (pPrimeCore 2 G) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact pPrimeCore_coprime_card.pow_left k
  exact hna (commutator_self_eq_bot_iff.mp
    (le_bot_iff.mp ((le_inf (commutator_le_self P) hc).trans hdis.le_bot)))

/-- Every automorphism fixes the central involution of the marked SD₁₆
Sylow subgroup when an odd Hall subgroup is cyclic. -/
theorem automorphism_fix_fourth_of_cyclic_odd_hall
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D)
    (S : Sylow 2 G) (a b : S)
    (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hc : b*a*b⁻¹ = a^3) (hg : closure ({a,b} : Set S) = ⊤)
    (φ : MulAut G) : φ ((a : G)^4) = (a : G)^4 := by
  classical
  have hna : ¬ IsMulCommutative S := by
    intro hcomm
    let := hcomm
    have he : a^3=a := by simpa only [mul_comm b a,mul_inv_cancel_right] using hc.symm
    have he2 : a^2=1 := mul_right_cancel
      (show a^2*a=1*a by simpa only [←pow_succ,one_mul] using he)
    have hd := orderOf_dvd_of_pow_eq_one he2
    rw [ha] at hd
    norm_num at hd
  have hcore := twoCore_ne_bot_of_cyclic_odd_hall hs D hD (S : Subgroup G) S.isPGroup' hna
  let z : G := (a : G)^4
  have hz : orderOf z=2 := by
    rw [show z=(a : G)^4 from rfl,orderOf_pow,orderOf_coe,ha]
    decide
  have hz1 : z ≠ 1 := fun he => by simp [he] at hz
  let : (zpowers z).Characteristic :=
    characteristic_zpowers_fourth_of_twoCore_ne_bot S a b ha hb hc hg hcore
  have hm : φ z ∈ zpowers z :=
    characteristic_iff_le_comap.mp inferInstance φ (mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf,hz] at hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
  have hi2 : i<2 := Finset.mem_range.mp hi
  interval_cases i
  · exact (hz1 (φ.injective ((by simpa using he.symm : φ z=1).trans φ.map_one.symm))).elim
  · simpa only [pow_one] using he.symm
end Semidihedral
