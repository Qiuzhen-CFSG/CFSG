module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.ElementaryEightSevenNormalizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.NormNum

/-!
# Automorphism subgroups of an elementary group of order eight

A subgroup of the automorphism group of a finite elementary abelian two-group
of order eight has order at most six if its Sylow two-subgroups have order two.
The public theorem retains the solvability hypothesis of its intended consumer,
although the proof does not need it. No normality or prescribed model subgroup
is assumed.

The imported automorphism count gives ambient order 168. Lagrange's theorem
and the Sylow two-order restrict the subgroup order to 2, 6, 14, or 42.
In either excessive case Sylow counting makes its seven-subgroup normal.
The original subgroup consequently lies in the ambient normalizer of that
seven-subgroup, contradicting the imported oddness of the normalizer order.
This supplies the elementary-core calculation used in Stellmacher Section 11,
`refs/latex/stellmacher-n-group.tex`, lines 2076–2081.
-/

universe u

private theorem small_card_candidates
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ∣ 168) (sylow : Sylow 2 G)
    (hsylow : Nat.card sylow = 2) :
    Nat.card G = 2 ∨ Nat.card G = 6 ∨ Nat.card G = 14 ∨ Nat.card G = 42 := by
  have htwo : 2 ∣ Nat.card G := by
    rw [← hsylow]
    exact sylow.toSubgroup.card_subgroup_dvd_card
  have hfour : ¬ 4 ∣ Nat.card G := by
    intro hfour
    have hbad := sylow.pow_dvd_card_of_pow_dvd_card (n := 2) hfour
    norm_num [hsylow] at hbad
  have hmem := Nat.mem_divisors.mpr ⟨hcard, by decide⟩
  have hdivisors : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hdivisors] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

private theorem normal_seven_of_card
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 14 ∨ Nat.card G = 42) (sylow : Sylow 7 G) :
    Nat.card sylow = 7 ∧ sylow.toSubgroup.Normal := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hsylow : Nat.card sylow = 7 := by
    rw [sylow.card_eq_multiplicity]
    rcases hcard with hcard | hcard
    · rw [hcard, show (14 : ℕ) = 2 * 7 by decide,
        Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, (show Nat.Prime 7 by decide).factorization]
    · rw [hcard, show (42 : ℕ) = 6 * 7 by decide,
        Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 6)]
      norm_num [(show Nat.Prime 7 by decide).factorization]
  refine ⟨hsylow, ?_⟩
  have hindex := sylow.toSubgroup.card_mul_index
  rw [hsylow] at hindex
  have hindex_le : sylow.toSubgroup.index ≤ 6 := by
    rcases hcard with hcard | hcard <;> omega
  have hcount_le : Nat.card (Sylow 7 G) ≤ 6 :=
    (Nat.le_of_dvd (by rcases hcard with hcard | hcard <;> omega)
      sylow.card_dvd_index).trans hindex_le
  have hmod := card_sylow_modEq_one 7 G
  have hcount : Nat.card (Sylow 7 G) = 1 := by
    change Nat.card (Sylow 7 G) % 7 = 1 % 7 at hmod
    omega
  have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hcount).1
  exact sylow.normal_of_subsingleton

private theorem card_le_six_of_card_dvd_168_of_odd_normalizers
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 168)
    (hnormalizer : ∀ subgroup : Subgroup G, Nat.card subgroup = 7 →
      Odd (Nat.card (Subgroup.normalizer (subgroup : Set G))))
    (H : Subgroup G) (hSylow : ∃ sylow : Sylow 2 H, Nat.card sylow = 2) :
    Nat.card H ≤ 6 := by
  obtain ⟨sylowTwo, hsylowTwo⟩ := hSylow
  have hdivides : Nat.card H ∣ 168 := hcard ▸ H.card_subgroup_dvd_card
  rcases small_card_candidates hdivides sylowTwo hsylowTwo with hsmall | hsmall | hlarge
  · omega
  · omega
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  let sylowSeven : Sylow 7 H := Classical.choice inferInstance
  obtain ⟨hseven, hnormal⟩ := normal_seven_of_card hlarge sylowSeven
  have : sylowSeven.toSubgroup.Normal := hnormal
  let seven : Subgroup G := sylowSeven.toSubgroup.map H.subtype
  have hseven_card : Nat.card seven = 7 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hseven
  have hle : H ≤ Subgroup.normalizer (seven : Set G) := by
    have hmap := sylowSeven.toSubgroup.le_normalizer_map H.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype]
      using hmap
  have htwo : 2 ∣ Nat.card (Subgroup.normalizer (seven : Set G)) := by
    apply dvd_trans (show 2 ∣ Nat.card H from ?_) (Subgroup.card_dvd_of_le hle)
    rcases hlarge with hlarge | hlarge <;> norm_num [hlarge]
  exact False.elim ((hnormalizer seven hseven_card).not_two_dvd_nat htwo)

public theorem card_le_six_of_elementary_eight_automorphisms
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (H : Subgroup (MulAut E)) [Group.IsSolvable H]
    (hSylow : ∃ sylow : Sylow 2 H, Nat.card sylow = 2) : Nat.card H ≤ 6 := by
  exact card_le_six_of_card_dvd_168_of_odd_normalizers
    (card_mulAut_of_elementary_eight E hE)
    (odd_card_normalizer_of_elementary_eight_seven E hE) H hSylow
