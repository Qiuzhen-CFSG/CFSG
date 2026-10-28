module
public import Theory.SpecificGroups.PSL2.FourNormalizer
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.InnerFourNormalizer
/-!
# Prime PSL₂ parameters under the actual cubic normalizer bound

An odd-field four-group is self centralizing. Its normalizer two-subgroups
have order at most eight, so index at most two bounds the Sylow order by
sixteen. For a Fermat or Mersenne prime, the adjacent power of two then
leaves only5,7,17. The automorphism version pulls back the literal inner
four; two-perfectness puts the prime-field cubic actor inside the inner
automorphism group. No ambient component absorption is assumed.

Source: Aschbacher–Smith, inspection before2.4.32, printed p.547.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- A two-subgroup normalizing a self-centralizing four has order at most eight. -/
theorem two_subgroup_normalizing_selfCentral_four_card_le_eight
    {G : Type*} [_root_.Group G] [Finite G] (V N : Subgroup G) [IsKleinFour V]
    (hself : centralizer (V : Set G) = V) (hp : IsPGroup 2 N)
    (hn : N ≤ normalizer (V : Set G)) : Nat.card N ≤ 8 := by
  have hk : Nat.card V.normalizerMonoidHom.ker = 4 := by
    rw [V.normalizerMonoidHom_ker,hself,
      Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv,IsKleinFour.card_four]
  have hr : Nat.card V.normalizerMonoidHom.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using V.normalizerMonoidHom.range.card_subgroup_dvd_card
  have hh := V.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker,hk] at hh
  have hdiv : Nat.card N ∣ 24 :=
    (card_dvd_of_le hn).trans (hh ▸ Nat.mul_dvd_mul_left 4 hr)
  obtain ⟨r,hr⟩ := hp.exists_card_eq
  have hco : Nat.Coprime (Nat.card N) 3 := by
    rw [hr]
    exact (by decide : Nat.Coprime 2 3).pow_left r
  have hd : Nat.card N ∣ 8 := hco.dvd_mul_right.mp hdiv
  exact Nat.le_of_dvd (by decide) hd

/-- A four-group whose normalizer has index at most two in a given Sylow
of odd PSL₂ bounds that Sylow order by sixteen. -/
theorem sylow_card_le_sixteen_of_four_normalizer_index
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (V : Subgroup PSL(2,F)) [IsKleinFour V] (P : Sylow 2 PSL(2,F))
    (hindex : ((normalizer (V : Set PSL(2,F))).subgroupOf P).index ≤ 2) :
    Nat.card P ≤ 16 := by
  let N := normalizer (V : Set PSL(2,F)) ⊓ (P : Subgroup PSL(2,F))
  have hN : Nat.card N ≤ 8 := two_subgroup_normalizing_selfCentral_four_card_le_eight
    V N (FourNormalizer.four_centralizer hF V) (P.isPGroup'.to_le inf_le_right) inf_le_left
  have he : Nat.card ((normalizer (V : Set PSL(2,F))).subgroupOf P) = Nat.card N := by
    rw [←inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe (show N ≤ (P : Subgroup _) from inf_le_right)).toEquiv
  have hh := ((normalizer (V : Set PSL(2,F))).subgroupOf P).card_mul_index
  rw [he] at hh
  nlinarith

private theorem adjacent_power_dvd_card {p k : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpk : p - 1 = 2^k ∨ p + 1 = 2^k) :
    2^k ∣ Nat.card PSL(2,ZMod p) := by
  have hp1 := (Fact.out : p.Prime).one_lt
  have hsub : 2 ∣ p - 1 := by obtain ⟨a,ha⟩ := hp; exact ⟨a,by omega⟩
  have hadd : 2 ∣ p + 1 := by obtain ⟨a,ha⟩ := hp; exact ⟨a+1,by omega⟩
  have hc := psl2_card_formula (ZMod p) ⟨p,1,Fact.out,hp,by omega,by simp⟩
  simp only [Nat.card_zmod] at hc
  rw [hc]
  have hs : p^2-1 = (p-1)*(p+1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
      Nat.sub_add_cancel (show 1 ≤ p^2 by nlinarith)]
  rw [hs]
  apply (Nat.dvd_div_iff_mul_dvd
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsub _) _)).mpr
  apply dvd_mul_of_dvd_right
  rcases hpk with h | h
  · rw [h,Nat.mul_comm (2^k) (p+1)]
    exact Nat.mul_dvd_mul hadd (dvd_refl _)
  · rw [h]
    exact Nat.mul_dvd_mul hsub (dvd_refl _)

/-- The actual four-normalizer bound leaves only prime parameters5,7,17
among the adjacent-power family. -/
theorem prime_parameter_of_four_normalizer_index {p k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpk : p - 1 = 2^k ∨ p + 1 = 2^k)
    (V : Subgroup PSL(2,ZMod p)) [IsKleinFour V] (P : Sylow 2 PSL(2,ZMod p))
    (hindex : ((normalizer (V : Set PSL(2,ZMod p))).subgroupOf P).index ≤ 2) :
    p = 5 ∨ p = 7 ∨ p = 17 := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hP := sylow_card_le_sixteen_of_four_normalizer_index
    (F := ZMod p) ⟨p,1,Fact.out,hodd,by omega,by simp⟩ V P hindex
  have hpow := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (adjacent_power_dvd_card hodd hpk))
  have hk : k ≤ 4 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (n := 2) (by omega) (show 5 ≤ k by omega)
    norm_num at hh
    omega
  have hp := Fact.out (p := p.Prime)
  have hple : p ≤ 17 := by rcases hpk with h | h <;> omega
  interval_cases p
  all_goals norm_num at hp
  all_goals norm_num
  all_goals interval_cases k <;> norm_num at hpk

/-- A two-perfect automorphism subgroup of prime PSL₂ is inner. -/
theorem prime_twoPerfect_le_inner {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (B : Subgroup (MulAut PSL(2,ZMod p))) (hB : IsPPerfect 2 B) :
    B ≤ (MulAut.conj : PSL(2,ZMod p) →* MulAut PSL(2,ZMod p)).range := by
  let I := (MulAut.conj : PSL(2,ZMod p) →* MulAut PSL(2,ZMod p)).range
  have hi : I.index = 2 := prime_card_inner_index (ZMod p)
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega) (by simp)
  let : I.Normal := I.normal_of_index_eq_two hi
  have hq : IsPGroup 2 (MulAut PSL(2,ZMod p) ⧸ I) :=
    IsPGroup.of_card (n := 1) (by rw [←index_eq_card,hi,pow_one])
  let f := (QuotientGroup.mk' I).comp B.subtype
  have he := hB.hom_eq_one_of_isPGroup hq f
  intro b hb
  exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun he ⟨b,hb⟩)

/-- The supplied faithful cubic actor and Sylow action screen the odd-prime
row down to5,7,17, through their literal inner four. -/
theorem prime_parameter_of_cubic_actor_normalizer_index
    {p k : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpk : p-1=2^k ∨ p+1=2^k)
    (B A : Subgroup (MulAut PSL(2,ZMod p))) (hB : IsPPerfect 2 B)
    [IsKleinFour (B.pCoreIn 2)] (P : Sylow 2 PSL(2,ZMod p))
    (hPA : (P : Subgroup PSL(2,ZMod p)).map MulAut.conj ≤ A)
    (hindex : (normalizer (B : Set (MulAut PSL(2,ZMod p)))).relIndex A ≤ 2) :
    p=5 ∨ p=7 ∨ p=17 := by
  obtain ⟨V,hV,_,hVindex⟩ := Theory.GroupTheory.inner_four_of_actor_normalizer_index (psl2_center_eq_bot _) B A
    (prime_twoPerfect_le_inner hp5 B hB) P hPA hindex
  let := hV
  exact prime_parameter_of_four_normalizer_index hp5 hpk V P hVindex
end Theory.PSL2
