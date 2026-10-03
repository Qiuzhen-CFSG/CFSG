module

public import Stellmacher.Recognition.LyonsU3Four.SylowQuarticCharacters
public import Stellmacher.Recognition.LyonsU3Four.NTwoLocalStructure
public import Theory.Character.RealOrderFourIntegral
public import Theory.Character.SimpleFaithfulCharacter
public import Theory.Character.IntegralRestriction
public import Theory.Character.Multiplicity

/-!
# Genuine Lyons Sylow restriction bounds

For an actual ambient character, the quartic Sylow character gives multiplicity
`(χ(1) - χ(t²)) / 16`. The principal multiplicities on the Sylow subgroup and
its center give the other two averages. Fusion and real order-four integrality
then give integer values and the congruence modulo four. For a nonprincipal
irreducible character, simplicity implies faithfulness, so the quartic
multiplicity is positive; the central average gives degree at least twelve.

The order-fifteen automizer is retained through `LocalCentralizerData`. No
character multiplicity, numerical constraint, or ambient table is assumed.
These direct statements leave the older conditional interfaces untouched.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 374 and
382, Lemmas 3 and 5; `refs/original/n-group-global/odd-core-rank-two-source/
lyons-u3four-1972-ams-wayback.pdf`.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four

private theorem character_eq_of_isConj {G : Type*} [Group G]
    {χ : ClassFunction G} (hχ : IsCharacter χ) {x y : G} (he : IsConj x y) :
    χ x = χ y := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  exact congrArg (characterClassFunction ρ) (ConjClasses.mk_eq_mk_iff_isConj.mpr he)

private theorem center_indicator_sum {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (c : ℂ) :
    (∑ s : S, if s ∈ Subgroup.center S then c else 0) = 4 * c := by
  have hc : (Finset.univ.filter (fun s : S => s ∈ Subgroup.center S)).card = 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact h.center_card
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  congr 1
  exact_mod_cast hc

private theorem central_value {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {χ : ClassFunction G} (hχ : IsCharacter χ)
    (t : S) (ht : orderOf t = 4) (s : S) (hs : s ∈ Subgroup.center S) (hs1 : s ≠ 1) :
    χ (s : G) = χ ((t : G)^2) := by
  let := h.center_elementary
  apply character_eq_of_isConj hχ (involutions_isConj S h ?_ ?_)
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian s hs) hs1
  · rw [orderOf_pow, Subgroup.orderOf_coe, ht]
    norm_num

/-- The three genuine restriction multiplicities, before extracting integer values. -/
public theorem sylow_restriction_multiplicities {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S)
    (d : LocalCentralizerData S) {χ : ClassFunction G} (hχ : IsCharacter χ)
    (t : S) (ht : orderOf t = 4) :
    ∃ m k l : ℕ,
      χ 1 - χ ((t : G)^2) = 16 * (m : ℂ) ∧
      χ 1 + 3 * χ ((t : G)^2) + 60 * χ (t : G) = 64 * (k : ℂ) ∧
      χ 1 + 3 * χ ((t : G)^2) = 4 * (l : ℂ) := by
  classical
  let z : S := t ^ 2
  have hzZ : z ∈ Subgroup.center S := square_mem_center S h t
  have hz1 : z ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by omega)
  let zi : QuarticCentralIndex S := ⟨⟨z, hzZ⟩, fun he => hz1 (congrArg Subtype.val he)⟩
  obtain ⟨u, hu⟩ := exists_order_fifteen_normalizer_action S h d.automizer_fifteen
  obtain ⟨θ, hθ⟩ := exists_sylowQuarticCharacter S h _ hu zi
  have hθchar : IsCharacter (fun s => θ (ConjClasses.mk s)) := by
    obtain ⟨n, ρ, rfl⟩ := hθ.irreducible.1
    exact ⟨n, ρ, rfl⟩
  let f : ClassFunction S := fun s => χ (s : G)
  have hf : IsCharacter f := isCharacter_comp_hom (S : Subgroup G).subtype hχ
  obtain ⟨m, hm⟩ := hf.scalarProduct_eq_nat hθchar
  obtain ⟨k, hk⟩ := hf.scalarProduct_eq_nat principal_isCharacter
  let e : Subgroup.center S →* G :=
    (S : Subgroup G).subtype.comp (Subgroup.center S).subtype
  obtain ⟨l, hl⟩ := (isCharacter_comp_hom e hχ).scalarProduct_eq_nat principal_isCharacter
  let n := χ 1
  let a := χ (t : G)
  let b := χ ((t : G)^2)
  have hc (s : S) (hs : s ∈ Subgroup.center S) (hs1 : s ≠ 1) : f s = b :=
    central_value S h hχ t ht s hs hs1
  have hnc (s : S) (hs : s ∉ Subgroup.center S) : f s = a := by
    apply character_eq_of_isConj hχ
    apply order_four_isConj_of_automizer_eq_fifteen S h d.automizer_fifteen
    · rw [Subgroup.orderOf_coe]
      exact (order_four_iff_not_mem_center S h s).mpr hs
    · rwa [Subgroup.orderOf_coe]
  have hone : f 1 = n := rfl
  have hpair (s : S) : f s * star (θ (ConjClasses.mk s)) =
      (if s = 1 then 4 * (n + b) else 0) +
      (if s = z then 8 * b else 0) +
      (if s ∈ Subgroup.center S then -4 * b else 0) := by
    rw [hθ.value]
    change f s * star (if s = 1 ∨ s = z then 4 else
      if s ∈ Subgroup.center S then -4 else 0) = _
    by_cases hs1 : s = 1
    · subst s; simp [hone, hz1.symm]; ring
    · by_cases hsz : s = z
      · subst s; simp [hz1, hzZ, hc z hzZ hz1]; ring
      · by_cases hsZ : s ∈ Subgroup.center S
        · simp [hs1, hsz, hsZ, hc s hsZ hs1]; ring
        · simp [hs1, hsz, hsZ]
  have hsumPair : (∑ s : S, f s * star (θ (ConjClasses.mk s))) = 4 * (n - b) := by
    simp_rw [hpair]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, center_indicator_sum S h]
    simp
    ring
  have hval (s : S) : f s = (if s = 1 then n - b else 0) +
      (if s ∈ Subgroup.center S then b - a else 0) + a := by
    by_cases hs1 : s = 1
    · subst s; simp [hone]
    · by_cases hsZ : s ∈ Subgroup.center S
      · simp [hs1, hsZ, hc s hsZ hs1]
      · simp [hs1, hsZ, hnc s hsZ]
  have hsum : (∑ s : S, f s) = n + 3 * b + 60 * a := by
    simp_rw [hval]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, center_indicator_sum S h]
    simp [← Nat.card_eq_fintype_card, h.card]
    ring
  have hzval (s : Subgroup.center S) : χ (e s) = (if s = 1 then n - b else 0) + b := by
    by_cases hs : s = 1
    · subst s; simp [e, n]
    · have hs' : (s : S) ≠ 1 := fun he => hs (Subtype.ext he)
      change f s = _
      rw [hc s s.property hs']
      simp [hs]
  have hsumZ : (∑ s : Subgroup.center S, χ (e s)) = n + 3 * b := by
    simp_rw [hzval]
    simp [Finset.sum_add_distrib, ← Nat.card_eq_fintype_card, h.center_card]
    ring
  change (Nat.card S : ℂ)⁻¹ * ∑ s : S, f s * star (θ (ConjClasses.mk s)) = _ at hm
  rw [h.card, hsumPair] at hm
  simp only [scalarProduct, Pi.one_apply, star_one, mul_one] at hk hl
  change (Nat.card S : ℂ)⁻¹ * ∑ s : S, f s = _ at hk
  rw [h.card, hsum] at hk
  rw [h.center_card, hsumZ] at hl
  refine ⟨m, k, l, ?_, ?_, ?_⟩
  · change n - b = _
    linear_combination 16 * hm
  · change n + 3*b + 60*a = _
    linear_combination 64 * hk
  · change n + 3*b = _
    linear_combination 4 * hl

/-- Integral values and the actual nonnegative restriction multiplicities.
The quartic pairing involves the degree minus the involution value. -/
public theorem genuine_sylow_character_constraints {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S)
    (d : LocalCentralizerData S) {χ : ClassFunction G} (hχ : IsCharacter χ)
    (t : S) (ht : orderOf t = 4) :
    ∃ (n : ℕ) (a b : ℤ) (m k : ℕ),
      χ 1 = (n : ℂ) ∧ χ (t : G) = (a : ℂ) ∧ χ ((t : G)^2) = (b : ℂ) ∧
      (n : ℤ) - b = 16 * (m : ℤ) ∧
      (n : ℤ) + 3*b + 60*a = 64 * (k : ℤ) ∧ Int.ModEq 4 a b := by
  have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
  have hzG : orderOf ((t : G)^2) = 2 := by rw [orderOf_pow, htG]; norm_num
  obtain ⟨a, ha⟩ := hχ.exists_int_of_fourth_power_of_isConj_inv (t : G)
    (htG ▸ pow_orderOf_eq_one (t : G))
    (order_four_isConj_of_automizer_eq_fifteen S h d.automizer_fifteen htG
      (by simpa using htG))
  obtain ⟨b, hb⟩ := hχ.exists_int_of_fourth_power_of_isConj_inv ((t : G)^2)
    (by rw [← pow_mul]; exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [htG]; norm_num))
    (involutions_isConj S h hzG (by simpa using hzG))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, χ 1 = (n : ℂ) := by
    obtain ⟨n, ρ, rfl⟩ := hχ
    exact ⟨n, by simp [Representation.char_one]⟩
  obtain ⟨m, k, l, hm, hk, _⟩ := sylow_restriction_multiplicities S h d hχ t ht
  rw [hn, hb] at hm
  rw [hn, hb, ha] at hk
  have hm' : (n : ℤ) - b = 16 * (m : ℤ) := by exact_mod_cast hm
  have hk' : (n : ℤ) + 3*b + 60*a = 64 * (k : ℤ) := by exact_mod_cast hk
  refine ⟨n, a, b, m, k, hn, ha, hb, hm', hk', ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨4 * (k : ℤ) - m - 4*a, ?_⟩
  omega

/-- Lyons's degree-twelve bound for a genuine nonprincipal irreducible character.
Faithfulness makes the quartic multiplicity positive, and averaging over the
center gives the remaining inequality. -/
public theorem genuine_nonprincipal_degree_ge_twelve {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S)
    (d : LocalCentralizerData S) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hnp : χ ≠ 1) (t : S) (ht : orderOf t = 4)
    {n : ℕ} (hn : χ 1 = (n : ℂ)) : 12 ≤ n := by
  obtain ⟨r, ρ, _, hρ, hfaith⟩ := hχ.exists_faithful_of_ne_one hnp
  have hc : IsCharacter χ := ⟨r, ρ, hρ⟩
  obtain ⟨m, k, l, hm, _, hl⟩ := sylow_restriction_multiplicities S h d hc t ht
  have hne : χ ((t : G)^2) ≠ χ 1 := by
    intro he
    rw [hρ] at he
    have hker := (ρ.mem_ker_iff_character_eq_degree ((t : G)^2)).mpr he
    have heq : (t : G)^2 = 1 := hfaith ((MonoidHom.mem_ker.mp hker).trans ρ.map_one.symm)
    have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
    exact pow_ne_one_of_lt_orderOf (by decide) (by omega) heq
  have hmpos : 0 < m := by
    by_contra! hm0
    have hm0' : m = 0 := by omega
    rw [hm0'] at hm
    exact hne (sub_eq_zero.mp (by simpa using hm)).symm
  rw [hn] at hm hl
  have hmR := congrArg Complex.re hm
  have hlR := congrArg Complex.re hl
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, zero_mul, sub_zero] at hmR hlR
  have hmRpos : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hlRpos : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hnR : (12 : ℝ) ≤ n := by linarith
  exact_mod_cast hnR

end Stellmacher.Recognition.LyonsU3Four
