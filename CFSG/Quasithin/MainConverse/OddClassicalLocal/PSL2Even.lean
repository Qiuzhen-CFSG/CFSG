module

public import CFSG.Quasithin.FermatMersenne
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeOrderCentralizerCore
public import GorensteinWalter.PSL2InvolutionFusion
public import GorensteinWalter.Section2.CentralizerZpowers

/-!
# Characteristic two for the Fermat–Mersenne PSL₂ groups

One of p − 1 and p + 1 is a power of two. Choose an involution in the
corresponding split or nonsplit torus. Huppert's normalizer calculation
makes its centralizer a two-group, and involution conjugacy gives this for
every involution. The prime-order centralizer criterion then makes the
two-core of every two-local subgroup self-centralizing. In particular, the
maximal two-locals containing Sylow subgroups satisfy condition E.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482; Huppert
II.8.3–4 for the torus normalizers. The bound is p ≥ 5, so both p = 5 and
p = 7 are included. No simplicity or pre-existing local-rank hypothesis is
needed in this calculation.
-/

namespace CFSG.Quasithin.MainConverse

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External GorensteinWalter

private theorem two_centralizers_of_torus
    (F : Type*) [Field F] [Finite F] (hodd : IsOddPrimePower (Nat.card F))
    (U : Subgroup (PSL2MatrixGroup F)) (heven : 2 ∣ Nat.card U)
    (hN : ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
      IsPGroup 2 (normalizer (R : Set (PSL2MatrixGroup F)))) :
    ∀ z : PSL2MatrixGroup F, orderOf z = 2 →
      IsPGroup 2 (centralizer ({z} : Set (PSL2MatrixGroup F))) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 heven
  have htG : orderOf (t : PSL2MatrixGroup F) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htne : (t : PSL2MatrixGroup F) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    contradiction
  have hct : IsPGroup 2 (centralizer ({(t : PSL2MatrixGroup F)} : Set _)) := by
    apply (hN (zpowers (t : PSL2MatrixGroup F)) (zpowers_le.mpr t.property) ?_).to_le
      (centralizer_singleton_le_normalizer_zpowers (t : PSL2MatrixGroup F))
    intro h
    apply htne
    exact mem_bot.mp (h ▸ mem_zpowers (t : PSL2MatrixGroup F))
  intro z hz
  have hzne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    contradiction
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd z t
    ⟨hzne, by simpa only [hz] using pow_orderOf_eq_one z⟩
    ⟨htne, by simpa only [htG] using pow_orderOf_eq_one (t : PSL2MatrixGroup F)⟩
  let e := MulAut.conj g
  have he : e z = t := hg
  let f : centralizer ({z} : Set (PSL2MatrixGroup F)) →*
      centralizer ({(t : PSL2MatrixGroup F)} : Set (PSL2MatrixGroup F)) :=
    ((e.toMonoidHom).comp (centralizer ({z} : Set _)).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change e (x : PSL2MatrixGroup F) * t = t * e (x : PSL2MatrixGroup F)
      have hx := congrArg e (mem_centralizer_singleton_iff.mp x.property)
      simpa only [map_mul, he] using hx)
  exact hct.of_injective f (by
    intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hab))

private theorem two_centralizers_of_adjacent_power (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : Odd p) {k : ℕ}
    (hpow : p - 1 = 2 ^ (k + 2) ∨ p + 1 = 2 ^ (k + 2)) :
    ∀ z : PSL2MatrixGroup F, orderOf z = 2 →
      IsPGroup 2 (centralizer ({z} : Set (PSL2MatrixGroup F))) := by
  have hFpow : Nat.card F = p ^ 1 := by simpa using hF
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 1, Fact.out, hp, by decide, hFpow⟩
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    rw [hF]
    exact Nat.gcd_eq_right ((Nat.Odd.sub_odd hp odd_one).two_dvd)
  rcases hpow with hminus | hplus
  · obtain ⟨U, _, hU, hN⟩ := huppert_II_8_3_split_torus_normalizer_card hFpow
    have hUcard : Nat.card U = 2 ^ (k + 1) := by
      rw [hU, hgcd, hF, hminus, show k + 2 = (k + 1) + 1 by omega, pow_succ,
        Nat.mul_div_left _ (by decide : 0 < 2)]
    apply two_centralizers_of_torus F hodd U
    · rw [hUcard, pow_succ]
      exact dvd_mul_left 2 _
    · intro R hRU hRne
      apply IsPGroup.of_card (n := k + 2)
      rw [hN R hRU hRne, hUcard, show k + 2 = (k + 1) + 1 by omega, pow_succ]
      exact Nat.mul_comm _ _
  · obtain ⟨U, w, _, hU, _, _, _, _, hcard, hN⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data hFpow
    have hUcard : Nat.card U = 2 ^ (k + 1) := by
      rw [hU, hgcd, hF, hplus, show k + 2 = (k + 1) + 1 by omega, pow_succ,
        Nat.mul_div_left _ (by decide : 0 < 2)]
    apply two_centralizers_of_torus F hodd U
    · rw [hUcard, pow_succ]
      exact dvd_mul_left 2 _
    · intro R hRU hRne
      apply IsPGroup.of_card (n := k + 2)
      rw [hN R hRU hRne, hcard, hUcard,
        show k + 2 = (k + 1) + 1 by omega, pow_succ]
      exact Nat.mul_comm _ _

private theorem adjacent_power {p : ℕ}
    (hp : CFSG.Quasithin.IsFermatOrMersennePrime p) (hp5 : 5 ≤ p) :
    ∃ k : ℕ, p - 1 = 2 ^ (k + 2) ∨ p + 1 = 2 ^ (k + 2) := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha2 : 2 ≤ 2 ^ a := by
      by_contra! h
      have hpos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
      have hone : 2 ^ a = 1 := by omega
      rw [hone] at ha
      norm_num at ha
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha2
    refine ⟨k, Or.inl ?_⟩
    rw [ha, Nat.add_sub_cancel, hk, Nat.add_comm 2 k]
  · have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha2
    exact ⟨k, Or.inr (by simpa [hk, Nat.add_comm 2 k] using ha)⟩

public theorem psl2_fermatMersenne_involution_centralizer_isPGroup (F : Type*) [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : CFSG.Quasithin.IsFermatOrMersennePrime p)
    (hp5 : 5 ≤ p) :
    ∀ z : PSL2MatrixGroup F, orderOf z = 2 →
      IsPGroup 2 (centralizer ({z} : Set (PSL2MatrixGroup F))) := by
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨k, hk⟩ := adjacent_power hp hp5
  exact two_centralizers_of_adjacent_power F hF (hp.1.odd_of_ne_two (by omega)) hk

/-- Every two-local of the actual prime-field model has self-centralizing
two-core; this includes all of the Sylow-containing maximal two-locals. -/
public theorem psl2_fermatMersenne_twoLocal_characteristicTwo
    (F : Type*) [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (M : Subgroup (PSL2MatrixGroup F)) (hM : IsTwoLocal M) :
    HasCharacteristicTwo M := by
  obtain ⟨Q, hQne, hQ, rfl⟩ := hM
  exact centralizer_pCore_le_of_prime_order_centralizers
    (psl2_fermatMersenne_involution_centralizer_isPGroup F hF hp hp5)
    Q (normalizer (Q : Set (PSL2MatrixGroup F))) hQ hQne Q.le_normalizer le_rfl

/-- The even-characteristic condition for the actual Fermat–Mersenne model. -/
public theorem psl2_fermatMersenne_evenCharacteristic
    (F : Type*) [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p) :
    IsEvenCharacteristic (PSL2MatrixGroup F) := by
  intro T M hM _
  exact psl2_fermatMersenne_twoLocal_characteristicTwo F hF hp hp5 M hM.1

end CFSG.Quasithin.MainConverse
