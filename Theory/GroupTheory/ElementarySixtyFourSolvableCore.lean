module

public import Theory.GroupTheory.ElementarySixtyFourPrimeCores
public import Theory.GroupTheory.ElementarySixtyFourThreeAutomorphisms
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# A nontrivial two-core for solvable binary six-dimensional groups

For a solvable automorphism subgroup B on an elementary binary group of
order at most 64, divisibility of |B| by 320 forces a nontrivial two-core.

The five- and thirty-one-cores vanish by the proved normalizer bounds.
Assuming the two-core trivial, a subgroup P of order five centralizes each
prime core: the only remaining primes are three and seven, and their
core automorphism orders are prime to five. Thus P centralizes the Fitting
subgroup. Solvable Fitting self-centralization places P inside that nilpotent
normal subgroup and hence inside the five-core, a contradiction.

The mathematical inputs are the coprime normalizer counts in
`ElementarySixtyFourPrimeCores`, the three-subgroup automorphism bound in
`ElementarySixtyFourThreeAutomorphisms`, and the solvable Fitting theorem in
`Fitting.Centralizer`.
-/

open Subgroup

private theorem centralizes_of_prime_card_not_dvd_aut
    {G : Type*} [Group G] [Finite G] (P N : Subgroup G) [N.Normal]
    {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p)
    (hnot : ¬ p ∣ Nat.card (MulAut N)) : P ≤ centralizer (N : Set G) := by
  let f : P →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp P.subtype
  have hdiv : Nat.card f.range ∣ p := hP ▸ Subgroup.card_range_dvd f
  have hcard : Nat.card f.range = 1 := by
    rcases (Nat.dvd_prime hp).mp hdiv with hh | hh
    · exact hh
    · exact (hnot (hh ▸ f.range.card_subgroup_dvd_card)).elim
  have hbot : f.range = ⊥ := Subgroup.card_eq_one.mp hcard
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hfx : f ⟨x, hx⟩ = 1 := mem_bot.mp (hbot ▸ (show f ⟨x, hx⟩ ∈ f.range from ⟨⟨x, hx⟩, rfl⟩))
  have heq := congrArg (fun a : MulAut N => (a ⟨y, hy⟩ : G)) hfx
  change x * y * x⁻¹ = y at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

private theorem prime_subgroup_le_core_of_le_fitting
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p P) (hP : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  let F := fittingSubgroup G
  let Q := P.subgroupOf F
  have hQ : IsPGroup p Q := hp.of_equiv (subgroupOfEquivOfLe hP).symm
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have hmap : Q.map F.subtype = P := map_subgroupOf_eq_of_le hP
  rw [← hmap]
  exact (map_mono hS).trans (S.map_le_pCore inferInstance inferInstance p)

/-- The remaining obstruction is a five-automorphism of a three-subgroup.
All other prime-core cases follow from normalizer bounds and solvable Fitting theory. -/
public theorem two_core_ne_bot_of_solvable_elementary_le_sixtyfour_of_three_aut_bound
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (B : Subgroup (MulAut E)) [Group.IsSolvable B]
    (hB : 320 ∣ Nat.card B)
    (hthree : ∀ A : Subgroup (MulAut E), IsPGroup 3 A →
      ¬ 5 ∣ Nat.card (MulAut A)) : pCore 2 B ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro htwo
  have hfive := five_core_eq_bot_of_elementary_card_le_sixtyfour hE B
    ((by decide : 16 ∣ 320).trans hB)
  have hthirtyone := thirtyone_core_eq_bot_of_elementary_card_le_sixtyfour hE B
    ((by decide : 2 ∣ 320).trans hB)
  have hcore (q : ℕ) (hq : q = 3 ∨ q = 7) : ¬ 5 ∣ Nat.card (MulAut (pCore q B)) := by
    let A := (pCore q B).map B.subtype
    have heq : Nat.card (MulAut (pCore q B)) = Nat.card (MulAut A) :=
      Nat.card_congr (MulAut.congr
        ((pCore q B).equivMapOfInjective B.subtype B.subtype_injective)).toEquiv
    rw [heq]
    rcases hq with rfl | rfl
    · exact hthree A ((pCore_isPGroup (p := 3) (G := B)).map B.subtype)
    · exact not_five_dvd_card_mulAut_seven_subgroup_of_elementary_card_le_sixtyfour
        hE A ((pCore_isPGroup (p := 7) (G := B)).map B.subtype)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 ((by decide : 5 ∣ 320).trans hB)
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, ha]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have hbotcentral : P ≤ centralizer ((⊥ : Subgroup B) : Set B) := by
    intro x _
    apply mem_centralizer_iff.mpr
    intro y hy
    have hyone : y = 1 := mem_bot.mp hy
    simp [hyone]
  have hcentral : P ≤ centralizer (fittingSubgroup B : Set B) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    have hq := prime_dvd_card_automorphisms_le_sixtyfour hE B
      (Nat.prime_of_mem_primeFactors q.val.property)
      (Nat.dvd_of_mem_primeFactors q.val.property)
    rcases hq with hq | hq | hq | hq | hq
    · simpa only [hq, htwo] using hbotcentral
    · rw [hq]
      exact centralizes_of_prime_card_not_dvd_aut P (pCore 3 B) (by decide) hP
        (hcore 3 (Or.inl rfl))
    · simpa only [hq, hfive] using hbotcentral
    · rw [hq]
      exact centralizes_of_prime_card_not_dvd_aut P (pCore 7 B) (by decide) hP
        (hcore 7 (Or.inr rfl))
    · simpa only [hq, hthirtyone] using hbotcentral
  have hle : P ≤ pCore 5 B := prime_subgroup_le_core_of_le_fitting P hp
    (hcentral.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance))
  have hbot : P = ⊥ := bot_unique (hfive ▸ hle)
  rw [hbot, card_bot] at hP
  norm_num at hP

/-- A solvable automorphism subgroup of an elementary binary group of order at most
64 whose order is divisible by 320 has a nontrivial two-core. -/
public theorem two_core_ne_bot_of_solvable_elementary_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (B : Subgroup (MulAut E)) [Group.IsSolvable B]
    (hB : 320 ∣ Nat.card B) : pCore 2 B ≠ ⊥ := by
  exact two_core_ne_bot_of_solvable_elementary_le_sixtyfour_of_three_aut_bound
    hE B hB (not_five_dvd_card_mulAut_three_subgroup_of_elementary_card_le_sixtyfour hE)
