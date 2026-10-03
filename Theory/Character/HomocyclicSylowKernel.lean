module

public import Theory.Character.CharacterKernel
public import Theory.Character.ConstantRestriction
public import Theory.Character.HomocyclicSylowDegree
public import Theory.Character.Multiplicity
public import Theory.PPrimeCore
public import Theory.Character.HomocyclicSylowColumns
public import Theory.Character.ModularBlock.InvolutionColumnVanishing
public import Theory.GroupTheory.PGroup.InvertingInvolution
public import Theory.LinearAlgebra.IntegerGramThree

/-!
# A proper normal overgroup of a homocyclic Sylow subgroup

Two nonprincipal characters constant with signed value on the nonidentity
elements of a subgroup, together with Brauer's degree and reciprocal-degree
relations, give a proper normal overgroup. The numerical theorem forces one
degree to be one. Its congruence modulo sixteen fixes its sign to minus one,
so the subgroup lies in the kernel of this nonprincipal linear character.

Source: R. Brauer, *Some applications of the theory of blocks of characters
of finite groups. II*, J. Algebra 1 (1964), §VI, p.319, (6.6)–(6.9).
The genuine principal-block columns and their integral Gram normal form
construct the two constant restrictions. The distinguished order-two linear
character is supported away from elements inverted by involutions. The
block-restricted involution identity therefore supplies the reciprocal-degree
relation. No odd-core hypothesis is used in this character argument; the
public endpoint retains it for the subsequent normality induction.
-/

public section

/-- Brauer's character identities supply a proper normal overgroup. The
characters and identities here are explicit hypotheses, not axioms asserting
their existence for homocyclic Sylow subgroups. -/
theorem exists_proper_normal_overgroup_of_character_relations
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (χ₁ χ₂ : ClassFunction G) (hχ₁ : IsCharacter χ₁) (hχ₂ : IsCharacter χ₂)
    (hne₁ : χ₁ ≠ 1) (hne₂ : χ₂ ≠ 1)
    (a b c d e f : ℤ)
    (hdegree₁ : χ₁ 1 = (a : ℂ)) (hdegree₂ : χ₂ 1 = (b : ℂ))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hma : 16 ∣ a + d) (hmb : 16 ∣ b + e)
    (hvalue₁ : ∀ g ∈ H, g ≠ 1 → χ₁ g = -(d : ℂ))
    (hvalue₂ : ∀ g ∈ H, g ≠ 1 → χ₂ g = -(e : ℂ))
    (hdeg : -1 + d * a + e * b + f * c = 0)
    (hrec : -(1 : ℚ) + d / (a : ℚ) + e / (b : ℚ) + 9 * f / (c : ℚ) = 0) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ H ≤ N := by
  rcases degree_eq_one_of_homocyclic_relations a b c d e f
      ha hb hc hd he hf hma hmb hdeg hrec with ha1 | hb1
  · have hd1 : d = -1 := by
      have hm := Int.emod_eq_zero_of_dvd hma
      omega
    apply hχ₁.exists_proper_normal_overgroup_of_degree_one H
      (by simpa only [ha1, Int.cast_one] using hdegree₁) hne₁
    intro g hg hgne
    simpa only [hd1, Int.cast_neg, Int.cast_one, neg_neg] using hvalue₁ g hg hgne
  · have he1 : e = -1 := by
      have hm := Int.emod_eq_zero_of_dvd hmb
      omega
    apply hχ₂.exists_proper_normal_overgroup_of_degree_one H
      (by simpa only [hb1, Int.cast_one] using hdegree₂) hne₂
    intro g hg hgne
    simpa only [he1, Int.cast_neg, Int.cast_one, neg_neg] using hvalue₂ g hg hgne

/-- The degree congruences follow from the constant restrictions themselves,
as soon as the subgroup order is divisible by sixteen. -/
theorem exists_proper_normal_overgroup_of_constant_character_relations
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hcard : 16 ∣ Nat.card H)
    (χ₁ χ₂ : ClassFunction G) (hχ₁ : IsCharacter χ₁) (hχ₂ : IsCharacter χ₂)
    (hne₁ : χ₁ ≠ 1) (hne₂ : χ₂ ≠ 1)
    (a b c d e f : ℤ)
    (hdegree₁ : χ₁ 1 = (a : ℂ)) (hdegree₂ : χ₂ 1 = (b : ℂ))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hvalue₁ : ∀ g ∈ H, g ≠ 1 → χ₁ g = -(d : ℂ))
    (hvalue₂ : ∀ g ∈ H, g ≠ 1 → χ₂ g = -(e : ℂ))
    (hdeg : -1 + d * a + e * b + f * c = 0)
    (hrec : -(1 : ℚ) + d / (a : ℚ) + e / (b : ℚ) + 9 * f / (c : ℚ) = 0) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ H ≤ N := by
  have hcardZ : (16 : ℤ) ∣ (Nat.card H : ℤ) := by exact_mod_cast hcard
  have hma : 16 ∣ a + d := by
    apply hcardZ.trans
    simpa only [sub_neg_eq_add] using
      hχ₁.card_dvd_degree_sub_of_constant H a (-d) hdegree₁ (by
        simpa only [Int.cast_neg] using hvalue₁)
  have hmb : 16 ∣ b + e := by
    apply hcardZ.trans
    simpa only [sub_neg_eq_add] using
      hχ₂.card_dvd_degree_sub_of_constant H b (-e) hdegree₂ (by
        simpa only [Int.cast_neg] using hvalue₂)
  exact exists_proper_normal_overgroup_of_character_relations H χ₁ χ₂ hχ₁ hχ₂
    hne₁ hne₂ a b c d e f hdegree₁ hdegree₂ ha hb hc hd he hf hma hmb
    hvalue₁ hvalue₂ hdeg hrec

open scoped BigOperators IsMulCommutative
open ModularBlock PrincipalBlockConstruction HomocyclicSylowColumns

attribute [local instance] Fintype.ofFinite

private theorem four_term_sum {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → ℤ) (i0 i1 i2 i3 : I) (d e f : ℤ)
    (h10 : i1 ≠ i0) (h20 : i2 ≠ i0) (h12 : i1 ≠ i2)
    (h30 : i3 ≠ i0) (h31 : i3 ≠ i1) (h32 : i3 ≠ i2)
    (hb : ∀ k, b k = if k = i0 then -1 else if k = i1 then d else
      if k = i2 then e else if k = i3 then f else 0) (F : I → ℂ) :
    ∑ k, (b k : ℂ) * F k = -F i0 + (d : ℂ) * F i1 +
      (e : ℂ) * F i2 + (f : ℂ) * F i3 := by
  have hp (k : I) : (b k : ℂ) * F k =
      (if k = i0 then -F i0 else 0) + (if k = i1 then (d : ℂ) * F i1 else 0) +
      (if k = i2 then (e : ℂ) * F i2 else 0) +
      (if k = i3 then (f : ℂ) * F i3 else 0) := by
    rw [hb]
    by_cases h0 : k = i0
    · subst k; simp [Ne.symm h10, Ne.symm h20, Ne.symm h30]
    by_cases h1 : k = i1
    · subst k; simp [h10, h12, Ne.symm h31]
    by_cases h2 : k = i2
    · subst k; simp [h20, Ne.symm h12, Ne.symm h32]
    by_cases h3 : k = i3
    · subst k; simp [h30, h31, h32]
    simp [h0, h1, h2, h3]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem distinguished_weighted_sum
    {G : Type*} [Group G] [Finite G] (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (D : ColumnSystem d S n) (J : G) (hJ : orderOf J = 2) :
    ∑ k ∈ d.block, (D.b ⟨0, by have := D.five_le; omega⟩ k : ℂ) *
      d.chi k (ConjClasses.mk J) ^ 2 / d.chi k (ConjClasses.mk 1) = 0 := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let j : Fin D.r := ⟨0, by have := D.five_le; omega⟩
  have hv := InvolutionColumnVanishing.principalBlock_involution_weighted_sum_eq_zero
    d S S.isPGroup' (D.ψ j - 1) J hJ (by
      intro q hq t ht hinv
      have ht2 : t ^ 2 = 1 := by
        have hh := ht.pow 2
        rw [← hJ, pow_orderOf_eq_one, isConj_one_right] at hh
        simpa only [hJ] using hh
      obtain ⟨m, hm⟩ := S.isPGroup'.exists_pow_pow_eq_one q
      have hq2 : q ^ 2 = 1 := by
        apply Subtype.ext
        exact S.square_eq_one_of_inverted_by_square_one
          (fun s _ => Subgroup.mem_center_iff.mpr (fun x => mul_comm x s))
          (congrArg Subtype.val hm) ht2 hinv
      exact hq (orbit_first_sub_one_eq_zero D.toOrbitSystem hn q hq2))
  convert hv using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.coefficient_eq j k hk]


private theorem character_data {G : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    IsCharacter (fun g => d.chi i (ConjClasses.mk g)) ∧
    ∃ a : ℤ, 0 < a ∧ d.chi i (ConjClasses.mk 1) = (a : ℂ) := by
  constructor
  · obtain ⟨m, ρ, hρ⟩ := (d.complete.1 i).1
    exact ⟨m, ρ, by funext g; rw [hρ]; rfl⟩
  · refine ⟨PGroupCartan.ordinaryDegree d i, ?_, ?_⟩
    · have hh := (d.complete.1 i).degree_re_pos
      rw [PGroupCartan.ordinaryDegree_eq] at hh
      exact_mod_cast hh
    · simpa using PGroupCartan.ordinaryDegree_eq d i

private theorem nonprincipal_character {G : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (i : d.I) (hi : i ≠ d.principal) :
    (fun g => d.chi i (ConjClasses.mk g)) ≠ (1 : ClassFunction G) := by
  intro he
  apply hi
  apply d.complete.2.2
  funext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  rw [d.principal_eq]
  exact congrFun he g

private theorem overgroup_of_columns
    {G : Type*} [Group G] [Finite G] (d : PrincipalCongruenceBlockData G)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (eS : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hcard : 16 ∣ Nat.card S) (D : ColumnSystem d S n) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ (S : Subgroup G) ≤ N := by
  classical
  obtain ⟨i1, i2, t, δ, ε, eps, h10, h20, h12, ht, hδ, hε, heps, hb⟩ :=
    IntegerGramThree.exists_normal_form D.five_le D.b d.principal D.principal D.gram
  let j : Fin D.r := ⟨0, by have := D.five_le; omega⟩
  let i3 := t j
  let f := eps j
  have hf : f = 1 ∨ f = -1 := heps j
  have hb1 (k) : D.b k i1 = δ := by simp [hb, h10]
  have hb2 (k) : D.b k i2 = ε := by
    simp [hb, h20, h12.symm]
  have hi1 : i1 ∈ d.block := by
    by_contra hh
    have hz := D.support j i1 hh
    rw [hb1] at hz
    rcases hδ with hh | hh <;> omega
  have hi2 : i2 ∈ d.block := by
    by_contra hh
    have hz := D.support j i2 hh
    rw [hb2] at hz
    rcases hε with hh | hh <;> omega
  have hsum (F : d.I → ℂ) :
      ∑ k ∈ d.block, (D.b j k : ℂ) * F k =
        -F d.principal + (δ : ℂ) * F i1 + (ε : ℂ) * F i2 + (f : ℂ) * F i3 := by
    calc
      _ = ∑ k, (D.b j k : ℂ) * F k := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp only [D.support j k hk, Int.cast_zero, zero_mul]
      _ = _ := four_term_sum (D.b j) d.principal i1 i2 i3 δ ε f
        h10 h20 h12 (ht j).1 (ht j).2.1 (ht j).2.2 (hb j) F
  obtain ⟨hχ1, a, ha, hda⟩ := character_data d i1
  obtain ⟨hχ2, b, hbpos, hdb⟩ := character_data d i2
  obtain ⟨_, c, hc, hdc⟩ := character_data d i3
  have hp (g : G) : d.chi d.principal (ConjClasses.mk g) = 1 := by
    rw [d.principal_eq]; rfl
  have hv1 (s : S) (hs : s ≠ 1) : d.chi i1 (ConjClasses.mk (s:G)) = -(δ : ℂ) :=
    D.reconstruction i1 hi1 δ hb1 s hs
  have hv2 (s : S) (hs : s ≠ 1) : d.chi i2 (ConjClasses.mk (s:G)) = -(ε : ℂ) :=
    D.reconstruction i2 hi2 ε hb2 s hs
  have hdegC : -(1 : ℂ) + δ * (a : ℂ) + ε * (b : ℂ) + f * (c : ℂ) = 0 := by
    have hh := D.sum_degree j
    rw [hsum, hp, hda, hdb, hdc] at hh
    exact hh
  have hdeg : -1 + δ * a + ε * b + f * c = 0 := by exact_mod_cast hdegC
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ⟩ := exists_prime_orderOf_dvd_card' (G := S) 2
    ((by norm_num : 2 ∣ 16).trans hcard)
  have hJ2 : (J:G) ^ 2 = 1 := by
    exact_mod_cast (show J ^ 2 = 1 by simpa only [hJ] using pow_orderOf_eq_one J)
  have hJne : J ≠ 1 := by intro hh; simp [hh] at hJ
  have hJG : orderOf (J:G) = 2 := by simpa only [Subgroup.orderOf_coe] using hJ
  have hv3 : d.chi i3 (ConjClasses.mk (J:G)) ^ 2 = 9 := by
    have hh := D.sum_square_one J hJ2
    change (∑ k ∈ d.block, (D.b j k : ℂ) * d.chi k (ConjClasses.mk (J:G))) = 0 at hh
    rw [hsum, hp, hv1 J hJne, hv2 J hJne] at hh
    rcases hδ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      rcases hf with hf | hf <;> norm_num [hf] at hh ⊢ <;>
      first
      | linear_combination (d.chi i3 (ConjClasses.mk (J:G)) + 3) * hh
      | linear_combination (3 - d.chi i3 (ConjClasses.mk (J:G))) * hh
  have hrecC : -(1 : ℂ) + δ / (a : ℂ) + ε / (b : ℂ) + 9 * f / (c : ℂ) = 0 := by
    have hh := distinguished_weighted_sum d S hn eS D J hJG
    change (∑ k ∈ d.block, (D.b j k : ℂ) * d.chi k (ConjClasses.mk (J:G)) ^ 2 /
      d.chi k (ConjClasses.mk 1)) = 0 at hh
    simp only [mul_div_assoc] at hh
    rw [hsum, hp, hp, hv1 J hJne, hv2 J hJne, hv3, hda, hdb, hdc] at hh
    rcases hδ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      norm_num at hh ⊢ <;> convert hh using 1 <;> ring
  have hrec : -(1 : ℚ) + δ / (a : ℚ) + ε / (b : ℚ) + 9 * f / (c : ℚ) = 0 := by
    exact_mod_cast hrecC
  apply exists_proper_normal_overgroup_of_constant_character_relations
    (S : Subgroup G) hcard _ _ hχ1 hχ2
    (nonprincipal_character d i1 h10) (nonprincipal_character d i2 h20)
    a b c δ ε f hda hdb ha hbpos hc hδ hε hf _ _ hdeg hrec
  · intro g hg hgne
    exact hv1 ⟨g, hg⟩ (fun hh => hgne (congrArg Subtype.val hh))
  · intro g hg hgne
    exact hv2 ⟨g, hg⟩ (fun hh => hgne (congrArg Subtype.val hh))

/-- Brauer's proper-normal-overgroup step for a rank-two homocyclic Sylow
two-subgroup with noncentralizing normalizer. The actual character columns
construct a nonprincipal linear character whose kernel contains the Sylow
subgroup. The odd-core hypothesis is retained for the normality-induction
interface, although this step does not require it. -/
theorem exists_proper_normal_overgroup_of_homocyclic_sylow
    {G : Type*} [Group G] [Finite G] (_hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hNC : ¬ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ (S : Subgroup G) ≤ N := by
  obtain ⟨d⟩ := exists_principalCongruenceBlockData G
  obtain ⟨D⟩ := exists_columnSystem d S hn e hNC
  have hcard : 16 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    change 16 ∣ Nat.card (ZMod (2 ^ n)) * Nat.card (ZMod (2 ^ n))
    rw [Nat.card_zmod, ← pow_add]
    exact (show 2 ^ 4 ∣ 2 ^ (n + n) from pow_dvd_pow 2 (by omega))
  exact overgroup_of_columns d S hn e hcard D
