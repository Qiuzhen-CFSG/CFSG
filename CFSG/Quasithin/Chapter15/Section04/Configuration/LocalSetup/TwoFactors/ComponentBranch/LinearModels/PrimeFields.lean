module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.LinearRingEquiv

/-!
# The prime-field fixed-action obstruction for PSL₂

A faithful four-group fixing a Sylow two-subgroup pointwise acts by inner
conjugation, by the prime-field projective automorphism calculation. A Klein
four inside the Sylow subgroup is self-centralizing, so the four conjugating
elements exhaust it and force the whole Sylow subgroup to be Klein four.

For primes congruent to ±7 modulo 16, the PSL₂ order formula instead makes
the Sylow order divisible by eight. For primes congruent to ±11 modulo 24,
the cyclic rotation torus in an involution centralizer has order divisible
by three. Its subgroup of order three is normal in that actual centralizer;
normality is relative to the fixed subgroup, not the ambient simple group.
The disjoint two- and three-cores then obstruct characteristic two.

The final statements transport the Sylow subgroup and its given action
through the coefficient-field equivalence, so they apply to any finite
field of prime cardinality and retain the actual matrix PSL₂ carrier.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18 (3)–(6),
printed pp.309–310, and the component paragraph of 15.4.18,
printed pp.1162–1163.
-/

public section

open Subgroup GorensteinWalter
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels

private theorem normal_three_not_characteristicTwo
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Nat.card N = 3) : ¬ HasCharacteristicTwo G := by
  intro h
  have hN3 : N ≤ pCore 3 G :=
    le_sSup ⟨inferInstance, IsPGroup.iff_card.mpr ⟨1, by simpa using hN⟩⟩
  have hN2 : N ≤ pCore 2 G := by
    intro x hx
    apply h
    apply mem_centralizer_iff.mpr
    intro y hy
    exact pCore_commute_of_ne 2 3 (by decide) y hy x (hN3 hx)
  have he : N = ⊥ := by
    apply le_bot_iff.mp
    have hi := le_inf hN2 hN3
    rwa [(pCore_disjoint_of_ne 2 3 (by decide)).eq_bot] at hi
  have := N.card_eq_one.mpr he
  omega

private theorem reflected_join_not_characteristicTwo
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (w : G) (hU : IsCyclic U)
    (h3 : 3 ∣ Nat.card U)
    (hinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) :
    ¬ HasCharacteristicTwo (U ⊔ zpowers w : Subgroup G) := by
  let : IsCyclic U := hU
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 h3
  let A : Subgroup G := zpowers (a : G)
  let D : Subgroup G := U ⊔ zpowers w
  have hAU : A ≤ U := zpowers_le.mpr a.property
  have hAD : A ≤ D := hAU.trans le_sup_left
  have hUN : U ≤ normalizer (A : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mul_comm' (⟨x, hAU hx⟩ : U) ⟨u, hu⟩)
  have hwN : w ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (zpowers (a : G)).map (MulAut.conj w).toMonoidHom = zpowers (a : G)
    rw [MonoidHom.map_zpowers]
    change zpowers (w * (a : G) * w⁻¹) = _
    rw [hinv _ a.property, zpowers_inv]
  let N := A.subgroupOf D
  have : N.Normal := (normal_subgroupOf_iff_le_normalizer hAD).mpr
    (sup_le hUN (zpowers_le.mpr hwN))
  apply normal_three_not_characteristicTwo N
  rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv, Nat.card_zpowers,
    Subgroup.orderOf_coe a, ha]

/-- In the ±11 modulo 24 cases, each inner involution has a fixed subgroup
with a nontrivial normal subgroup of order three. -/
theorem prime_residue_involution_not_characteristicTwo
    (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (hres : Nat.card F % 24 = 11 ∨ Nat.card F % 24 = 13)
    {t : PSL2 F} (ht : IsInvolution t) :
    ¬ HasCharacteristicTwo (centralizer ({t} : Set (PSL2 F))) := by
  obtain ⟨U, w, hU, _, _, _, hinv, hC, hEven, hcard⟩ :=
    psl2_reflected_torus_card hF ht
  rw [hC]
  apply reflected_join_not_characteristicTwo U w hU _ hinv
  rcases hEven with ⟨k, hk⟩
  rcases hres with hres | hres <;> rcases hcard with hcard | hcard <;>
    omega

private theorem prime_sylow_klein_of_four_fixers
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p)
    (P : Sylow 2 PSL(2, ZMod p))
    {A : Type*} [Group A] [Finite A] (hA : Nat.card A = 4)
    (ρ : A →* MulAut PSL(2, ZMod p)) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x ∈ P, ρ a x = x) : IsKleinFour P := by
  classical
  let hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod p) hF P
  obtain ⟨V, hVP, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup PSL(2, ZMod p)) hm e
  have hinner (a : A) : ∃ v : V, ρ a = MulAut.conj (v : PSL(2, ZMod p)) := by
    obtain ⟨x, _, hx⟩ := Theory.PSL2.primeField_sylow_fixed_inner hp hlarge P (ρ a) (hfix a)
    have hxV : x ∈ V := by
      rw [← psl2_kleinFour_centralizer_eq_self (ZMod p) hF V hV]
      apply mem_centralizer_iff.mpr
      intro v hv
      have hh := hfix a v (hVP hv)
      rw [hx, MulAut.conj_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact ⟨⟨x, hxV⟩, hx⟩
  choose f hf using hinner
  have hfi : Function.Injective f := by
    intro a b hab
    apply hρ
    rw [hf a, hf b, hab]
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfi, hA.trans hV.card_four.symm⟩).2
  have hPV : (P : Subgroup PSL(2, ZMod p)) ≤ V := by
    rw [← psl2_kleinFour_centralizer_eq_self (ZMod p) hF V hV]
    intro x hx
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨a, ha⟩ := hfs ⟨v, hv⟩
    have hh := hfix a x hx
    rw [hf a, ha, MulAut.conj_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have heq : (P : Subgroup PSL(2, ZMod p)) = V := le_antisymm hPV hVP
  exact heq.symm ▸ hV

private theorem prime_sylow_card_ne_four_of_residue
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hres : p % 16 = 7 ∨ p % 16 = 9)
    (P : Sylow 2 PSL(2, ZMod p)) : Nat.card P ≠ 4 := by
  intro hP
  have hsquare : p ^ 2 % 16 = 1 := by
    rw [Nat.pow_mod]
    rcases hres with h | h <;> rw [h]
  have h16 : 16 ∣ p ^ 2 - 1 := by omega
  have hcard : 2 ^ 3 ∣ Nat.card PSL(2, ZMod p) := by
    rw [psl2_card_formula (ZMod p) ⟨p, 1, Fact.out, hp, by omega, by simp⟩]
    simp only [Nat.card_zmod]
    have hd : 16 ∣ p * (p ^ 2 - 1) := dvd_mul_of_dvd_right h16 p
    exact (Nat.dvd_div_iff_mul_dvd (dvd_trans (by decide : 2 ∣ 16) hd)).mpr hd
  have hh := P.pow_dvd_card_of_pow_dvd_card hcard
  rw [hP] at hh
  norm_num at hh

/-- The prime-field fixed-action obstruction on the canonical prime field. -/
theorem primeField_fixed_action_false_zmod
    {p : ℕ} [Fact p.Prime]
    (hres : (p % 24 = 11 ∨ p % 24 = 13) ∨ (p % 16 = 7 ∨ p % 16 = 9))
    (P : Sylow 2 PSL(2, ZMod p))
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (ρ : A →* MulAut PSL(2, ZMod p)) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x ∈ P, ρ a x = x)
    (hchar : CharacteristicTwoFixed ρ) : False := by
  have hlarge : 3 < p := by rcases hres with (h | h) | (h | h) <;> omega
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let : IsKleinFour P := prime_sylow_klein_of_four_fixers hp hlarge P hA ρ hρ hfix
  rcases hres with hres | hres
  · let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    obtain ⟨t, htP, ht⟩ := Theory.PSL2.primeField_sylow_fixed_inner hp hlarge P (ρ a) (hfix a)
    have htne : t ≠ 1 := by
      intro he
      apply ha
      apply hρ
      simpa [he] using ht
    have htI : IsInvolution t := ⟨htne, by
      simpa [pow_two] using congrArg Subtype.val (IsKleinFour.mul_self (⟨t, htP⟩ : P))⟩
    have hc := hchar a ha
    rw [ht, MulAut.fixedSubgroup_conj] at hc
    exact prime_residue_involution_not_characteristicTwo (ZMod p)
      ⟨p, 1, Fact.out, hp, by omega, by simp⟩ (by simpa using hres) htI hc
  · exact prime_sylow_card_ne_four_of_residue hp hres P IsKleinFour.card_four

/-- The obstruction on any finite field of prime cardinality, with its actual
PSL₂ carrier and the given faithful action. -/
theorem primeField_fixed_action_false
    (F : Type*) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p)
    (hres : (p % 24 = 11 ∨ p % 24 = 13) ∨ (p % 16 = 7 ∨ p % 16 = 9))
    (P : Sylow 2 PSL(2, F))
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (ρ : A →* MulAut PSL(2, F)) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x ∈ P, ρ a x = x)
    (hchar : CharacteristicTwoFixed ρ) : False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime F hp (by simpa [Nat.card_eq_fintype_card] using hcard)).symm
  let e := psl2RingEquiv eF
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let σ : A →* MulAut PSL(2, ZMod p) := (MulAut.congr e).toMonoidHom.comp ρ
  apply primeField_fixed_action_false_zmod hres Q hA σ
    ((MulAut.congr e).injective.comp hρ) _ (characteristicTwoFixed_congr e ρ hchar)
  intro a y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change e (ρ a (e.symm (e x))) = e x
  rw [e.symm_apply_apply, hfix a x hx]

/-- Some nonidentity actor has a fixed subgroup whose two-core is not
self-centralizing, for precisely the prime-field restrictions in F.6.18. -/
theorem primeField_exists_non_characteristicTwo_fixed
    (F : Type*) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p)
    (hres : (p % 24 = 11 ∨ p % 24 = 13) ∨ (p % 16 = 7 ∨ p % 16 = 9))
    (P : Sylow 2 PSL(2, F))
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (ρ : A →* MulAut PSL(2, F)) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x ∈ P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧ ¬ HasCharacteristicTwo (ρ a).fixedSubgroup := by
  classical
  by_contra h
  apply primeField_fixed_action_false F hp hcard hres P hA ρ hρ hfix
  intro a ha
  by_contra hn
  exact h ⟨a, ha, hn⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
