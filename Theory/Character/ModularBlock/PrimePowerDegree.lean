module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.BrauerTuanAveraging
public import Theory.Character.BurnsideIntegrality
public import Theory.Character.BurnsideScalar
public import Theory.Character.SimpleFaithful
public import Theory.GroupTheory.ConjugacyClassSize
public import Mathlib.GroupTheory.Sylow

/-!
# Prime-power character degrees and congruence blocks

If a character vanishes on the nonidentity elements of a subgroup of order
divisible by `p`, and those elements have conjugacy classes of size prime to
`p`, then every character in its congruence block has degree divisible by `p`.
Central-character congruences put their values in the chosen prime ideal;
averaging over the subgroup puts their degrees in that ideal. Lying over
then gives divisibility in the natural numbers.

The center of a Sylow subgroup supplies such a subgroup whenever `p` divides
the group order. Thus it suffices to establish vanishing on nonidentity
classes of size prime to `p`. For a simple group and an irreducible character
of degree `p ^ r > 1`, normalized character values on these classes are integral.
Burnside's scalar-or-zero theorem and faithfulness give the required vanishing:
a scalar image would force a nonidentity element into the center. Consequently
every degree in this character's congruence block is divisible by `p`.

Source: Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51
(1945), Lemma 2 and its proof, pp.763--764.
-/

public section
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
open ModularBlock.BlockPreliminaries
open ModularBlock.PrimeBlockConstruction

namespace ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData
variable {p : ℕ} {G : Type*} [Group G] [Finite G]

private theorem natCast_mem_primeIdeal_iff (d : PrimeCongruenceBlockData p G) (n : ℕ) :
    (n : cyclotomicOrder d.eta) ∈ d.primeIdeal ↔ p ∣ n := by
  let : d.primeIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := d.primeIdeal_liesOver
  have h := Ideal.mem_of_liesOver d.primeIdeal (Ideal.span ({(p : ℤ)} : Set ℤ)) (n : ℤ)
  simpa only [map_natCast, Ideal.mem_span_singleton, Int.natCast_dvd_natCast] using h.symm

/-- The congruence and averaging step for a block with a vanishing row. -/
theorem degree_dvd_of_subgroup_vanishing (d : PrimeCongruenceBlockData p G)
    (i : d.I) (H : Subgroup G) (hH : p ∣ Nat.card H)
    (hclass : ∀ x : H, x ≠ 1 → ¬ p ∣ Nat.card (ConjClasses.mk (x : G)).carrier)
    (hvanish : ∀ x : H, x ≠ 1 → d.chi i (ConjClasses.mk (x : G)) = 0) :
    ∀ j ∈ d.blockOf i, ∃ n : ℕ, d.chi j (ConjClasses.mk 1) = (n : ℂ) ∧ p ∣ n := by
  classical
  intro j hj
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 j).1
  have hdegree : d.chi j (ConjClasses.mk 1) = (n : ℂ) := by
    rw [hρ]
    change ρ.character 1 = (n : ℂ)
    simp
  refine ⟨n, hdegree, ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let A := cyclotomicOrder d.eta
  let v : G → A := fun x => ⟨d.chi j (ConjClasses.mk x), by
    rw [hρ]
    exact representation_character_mem_cyclotomicOrder d.eta_spec ρ x⟩
  have hv1 : v 1 = (n : A) := Subtype.ext hdegree
  have hv (x : H) (hx : x ≠ 1) : v x ∈ d.primeIdeal := by
    have hc := (d.mem_blockOf_iff_centralCharacter j i).mp hj (ConjClasses.mk (x : G))
    have hzero : centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
        (d.complete.1 i) (ConjClasses.mk (x : G)) = 0 := by
      apply Subtype.ext
      simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue, hvanish x hx]
    rw [hzero, sub_zero] at hc
    have heq : centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
        (d.complete.1 j) (ConjClasses.mk (x : G)) * (n : A) =
          (Nat.card (ConjClasses.mk (x : G)).carrier : A) * v x := by
      apply Subtype.ext
      change (↑(Nat.card (ConjClasses.mk (x : G)).carrier) *
        d.chi j (ConjClasses.mk (x : G)) / d.chi j (ConjClasses.mk 1)) * (n : ℂ) = _
      rw [hdegree, div_mul_cancel₀ _ hnC]
      rfl
    have hmul := d.primeIdeal.mul_mem_right (n : A) hc
    rw [heq] at hmul
    exact (d.primeIdeal_maximal.isPrime.mem_or_mem hmul).resolve_left
      (fun h => hclass x hx ((d.natCast_mem_primeIdeal_iff _).mp h))
  obtain ⟨m, hm⟩ := BrauerTuan.character_subgroup_average_eq_nat (d.complete.1 j).1 H
  have hcardC : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : (∑ x : H, v x) = (Nat.card H : A) * (m : A) := by
    apply Subtype.ext
    rw [show (↑(∑ x : H, v x) : ℂ) = ∑ x : H, d.chi j (ConjClasses.mk (x : G)) from
      map_sum (A.subtype) _ _]
    convert (div_eq_iff hcardC).mp hm |>.trans (mul_comm _ _) using 1
    · congr 1
      ext; simp
    · simp
  have hsum_mem : (∑ x : H, v x) ∈ d.primeIdeal := by
    rw [hsum]
    exact d.primeIdeal.mul_mem_right _ ((d.natCast_mem_primeIdeal_iff _).mpr hH)
  let q := Ideal.Quotient.mk d.primeIdeal
  have hsumq : (∑ x : H, q (v x)) = q (v 1) := by
    apply Finset.sum_eq_single (1 : H)
    · intro x _ hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv x hx)
    · simp
  have hnmem : (n : A) ∈ d.primeIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hv1, ← hsumq, ← map_sum]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hsum_mem
  exact (d.natCast_mem_primeIdeal_iff n).mp hnmem

/-- Vanishing on nonidentity classes of size prime to `p` forces all degrees
in the same block to be divisible by `p`. -/
theorem degree_dvd_of_vanishing_on_prime_coprime_classes [Fact p.Prime]
    (d : PrimeCongruenceBlockData p G) (i : d.I) (hpG : p ∣ Nat.card G)
    (hv : ∀ x : G, x ≠ 1 → ¬ p ∣ Nat.card (ConjClasses.mk x).carrier →
      d.chi i (ConjClasses.mk x) = 0) :
    ∀ j ∈ d.blockOf i, ∃ n : ℕ, d.chi j (ConjClasses.mk 1) = (n : ℂ) ∧ p ∣ n := by
  let S : Sylow p G := Classical.choice inferInstance
  let Z := Subgroup.center S
  let H : Subgroup G := Z.map (S : Subgroup G).subtype
  have hSn : Nontrivial S :=
    (S : Subgroup G).nontrivial_iff_ne_bot.mpr (S.ne_bot_of_dvd_card hpG)
  let := hSn
  let : Nontrivial Z := S.2.center_nontrivial
  have hZp := S.2.to_subgroup Z
  obtain ⟨a, ha, he⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have hH : p ∣ Nat.card H := by
    rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, he]
    exact dvd_pow_self p (Nat.ne_of_gt ha)
  have hclass (x : H) : ¬ p ∣ Nat.card (ConjClasses.mk (x : G)).carrier := by
    obtain ⟨z, hz, hzx⟩ := x.property
    have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      intro y hy
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← hzx]
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)
    rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
    exact fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hSC))
  apply d.degree_dvd_of_subgroup_vanishing i H hH (fun x _ => hclass x)
  intro x hx
  exact hv x (fun he => hx (Subtype.ext he)) (hclass x)

/-- Brauer--Tuan Lemma 2, degree-divisibility consequence for simple groups:
if an irreducible character has degree a positive power of `p`, every character
in its congruence block has degree divisible by `p`. -/
theorem degree_dvd_of_prime_power_degree [IsSimpleGroup G] [hp : Fact p.Prime]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I) (r : ℕ) (hr : 0 < r)
    (hdegree : d.chi i (ConjClasses.mk 1) = ((p ^ r : ℕ) : ℂ)) :
    ∀ j ∈ d.blockOf i, ∃ n : ℕ, d.chi j (ConjClasses.mk 1) = (n : ℂ) ∧ p ∣ n := by
  obtain ⟨n, ρ, he⟩ := (d.complete.1 i).1
  have hn : n = p ^ r := by
    have heval : d.chi i (ConjClasses.mk 1) = (n : ℂ) := by
      rw [he]
      change ρ.character 1 = (n : ℂ)
      simp
    exact_mod_cast heval.symm.trans hdegree
  have hρ : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one ρ).mpr
    simpa [he] using (d.complete.1 i).2
  let := hρ
  have hdim : 1 < Module.finrank ℂ (Fin n → ℂ) := by
    simpa [hn] using one_lt_pow₀ hp.out.one_lt hr.ne'
  have hfaith := ρ.injective_of_isSimpleGroup_of_one_lt_finrank hdim
  have hpG : p ∣ Nat.card G := by
    have hdvd := irreducible_dimension_dvd_group_order ρ
    simp only [Module.finrank_pi, Fintype.card_fin, hn] at hdvd
    exact (dvd_pow_self p hr.ne').trans hdvd
  apply d.degree_dvd_of_vanishing_on_prime_coprime_classes i hpG
  intro x hx hclass
  have hc : (Module.finrank ℂ (Fin n → ℂ)).Coprime
      (Nat.card (ConjClasses.mk x).carrier) := by
    simpa [hn] using (hp.out.coprime_pow_of_not_dvd hclass (m := r)).symm
  have hi := ρ.isIntegral_character_div_finrank_of_coprime_class_card x hc
  have hpow : ρ x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have ho := burnside_scalar_or_zero n (ρ x) (orderOf x) (orderOf_pos x).ne' hpow
    (by simpa [Representation.character] using hi)
  rcases ho with hzero | ⟨z, hz⟩
  · rw [he]
    exact hzero
  · have hcentral : x ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply hfaith
      simp only [map_mul, hz]
      ext v
      simp
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hc | hc
    · exact (hx (by simpa [hc] using hcentral)).elim
    · let : IsMulCommutative G := (Subgroup.center_eq_top_iff.mp hc)
      have hdim1 := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
      omega

end ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData
