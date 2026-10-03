module

public import GorensteinWalter.PGL2DerivedSubgroup
public import Theory.SpecificGroups.SL2.NoIndexTwo
public import GorensteinWalter.LinearRingEquiv
public import Mathlib.Tactic

/-!
# Rigidity and index-two properties of odd PSL2 models

The order formula q(q^2-1)/2 determines the odd field order of a finite
PSL2 model. Such models have no normal subgroup of index two, by pulling
back to SL2 and using transvection generation in odd characteristic. These properties
transport across group isomorphisms. The derived subgroup of an odd PGL2
model is PSL2, including the explicit S4-to-A4 calculation at q=3.

These are the model-level inputs to the unique normal PSL2 core in
ABG Chapter II, Section3, Proposition2 (article p22). The argument preserves
the nonperfect q=3 case, using the existing projective order formulas and
the explicit field-three permutation models.
-/

public section
noncomputable section
namespace GorensteinWalter

universe u

theorem odd_prime_power_three_le (q : ℕ) (hq : IsOddPrimePower q) :
    3 ≤ q := by
  rcases hq with ⟨p, n, hp, hpodd, hn, rfl⟩
  have hpne : p ≠ 2 := by
    intro h
    subst p
    exact hpodd.not_two_dvd_nat (by simp)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  calc
    3 ≤ p := hp3
    _ = p ^ 1 := by simp
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn

private theorem psl2_order_parameter_injective
    {q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r)
    (heq : q * (q ^ 2 - 1) / 2 = r * (r ^ 2 - 1) / 2) :
    q = r := by
  have hqoddprod : 2 ∣ q * (q ^ 2 - 1) := by
    by_cases hqeven : Even q
    · exact dvd_mul_of_dvd_left hqeven.two_dvd _
    · have hqodd : Odd q := Nat.not_even_iff_odd.mp hqeven
      exact dvd_mul_of_dvd_right
        (Nat.Odd.sub_odd hqodd.pow (show Odd (1 : ℕ) from odd_one)).two_dvd q
  have hroddprod : 2 ∣ r * (r ^ 2 - 1) := by
    by_cases hreven : Even r
    · exact dvd_mul_of_dvd_left hreven.two_dvd _
    · have hrodd : Odd r := Nat.not_even_iff_odd.mp hreven
      exact dvd_mul_of_dvd_right
        (Nat.Odd.sub_odd hrodd.pow (show Odd (1 : ℕ) from odd_one)).two_dvd r
  have heq' : q * (q ^ 2 - 1) = r * (r ^ 2 - 1) := by
    calc
      q * (q ^ 2 - 1) = (q * (q ^ 2 - 1) / 2) * 2 :=
        (Nat.div_mul_cancel hqoddprod).symm
      _ = (r * (r ^ 2 - 1) / 2) * 2 := by rw [heq]
      _ = r * (r ^ 2 - 1) := Nat.div_mul_cancel hroddprod
  by_contra hne
  have hqpos : 0 < q ^ 2 := pow_pos (by omega) _
  have hrpos : 0 < r ^ 2 := pow_pos (by omega) _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hq2 : q ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hlt (by omega)
    have hqprod : q * (q ^ 2 - 1) < r * (r ^ 2 - 1) := by
      exact Nat.mul_lt_mul_of_pos_left (by omega : q ^ 2 - 1 < r ^ 2 - 1)
        (by omega : 0 < q) |>.trans_le (Nat.mul_le_mul_right _ (Nat.le_of_lt hlt))
    exact (Nat.ne_of_lt hqprod) heq'
  · have hr2 : r ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hgt (by omega)
    have hrprod : r * (r ^ 2 - 1) < q * (q ^ 2 - 1) := by
      exact Nat.mul_lt_mul_of_pos_left (by omega : r ^ 2 - 1 < q ^ 2 - 1)
        (by omega : 0 < r) |>.trans_le (Nat.mul_le_mul_right _ (Nat.le_of_lt hgt))
    exact (Nat.ne_of_lt hrprod) heq'.symm

theorem psl2_field_card_eq_of_card_eq
    (K E : Type u) [Field K] [Finite K] [Field E] [Finite E]
    (hK : IsOddPrimePower (Nat.card K))
    (hE : IsOddPrimePower (Nat.card E))
    (hcard : Nat.card (PSL2 K) = Nat.card (PSL2 E)) :
    Nat.card K = Nat.card E := by
  apply psl2_order_parameter_injective
      (odd_prime_power_three_le _ hK) (odd_prime_power_three_le _ hE)
  rw [← psl2_card_formula K hK, ← psl2_card_formula E hE]
  exact hcard

theorem psl2_card_ge_sixty_of_card_gt_three
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    60 ≤ Nat.card (PSL2 K) := by
  let q := Nat.card K
  have hqodd : Odd q := by
    rcases hK with ⟨p, n, _hp, hpodd, _hn, hp⟩
    change Odd (Nat.card K)
    rw [hp]
    exact hpodd.pow
  have hq5 : 5 ≤ q := by
    rcases hqodd with ⟨a, ha⟩
    omega
  have hdiv : 2 ∣ q * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right
      (Nat.Odd.sub_odd hqodd.pow (show Odd (1 : ℕ) from odd_one)).two_dvd q
  rw [psl2_card_formula K hK]
  change 60 ≤ q * (q ^ 2 - 1) / 2
  have hprod : 120 ≤ q * (q ^ 2 - 1) := by
    have hsq : 25 ≤ q ^ 2 := by nlinarith
    have hsub : 24 ≤ q ^ 2 - 1 := by omega
    exact Nat.mul_le_mul hq5 hsub
  omega

theorem psl2_no_normal_index_two
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ∀ N : Subgroup (PSL2 K), N.Normal → N.index ≠ 2 := by
  let : Fintype K := Fintype.ofFinite K
  rcases hK with ⟨p, n, hp, hpOdd, _hn, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using hcard)
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hzero
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv
    subst p
    exact hpOdd.not_two_dvd_nat (by simp)
  intro N _hNnormal hNindex
  let f : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2 K :=
    QuotientGroup.mk' (Subgroup.center _)
  have hcomap : (N.comap f).index = 2 := by
    rw [N.index_comap_of_surjective (QuotientGroup.mk'_surjective _)]
    exact hNindex
  exact Matrix.SpecialLinearGroup.index_ne_two htwo (N.comap f) hcomap

theorem no_normal_index_two_of_mulEquiv_psl2
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hNnormal hNindex
  let N' : Subgroup (PSL2 K) := N.map e.toMonoidHom
  have hN'normal : N'.Normal := by
    exact (e.normal_map_iff).2 hNnormal
  have hN'index : N'.index = 2 := by
    change (N.map (e : G →* PSL2 K)).index = 2
    rw [Subgroup.index_map_equiv]
    exact hNindex
  exact psl2_no_normal_index_two K hK N' hN'normal hN'index

theorem commutator_mulEquiv_psl2_of_mulEquiv_pgl2
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PGL2 K) :
    Nonempty (commutator G ≃* PSL2 K) := by
  have hge : 3 ≤ Nat.card K := odd_prime_power_three_le _ hK
  by_cases hcard3 : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let eP : G ≃* Equiv.Perm (Fin 4) :=
      (e.trans (pgl2RingEquiv eK).symm).trans pgl2_three_equiv_perm
    let eA : commutator G ≃* alternatingGroup (Fin 4) :=
      (commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four eP).some
    exact ⟨eA.trans
      (psl2_three_equiv_alternatingGroup.symm.trans (psl2RingEquiv eK))⟩
  · exact commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK (by omega) e

end GorensteinWalter

