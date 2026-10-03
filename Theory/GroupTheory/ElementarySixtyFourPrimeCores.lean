module

public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.ElementaryThirtyTwoThirtyOneNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.PGroupCore

/-!
# Prime-core restrictions in binary dimension at most six

The order of every automorphism subgroup divides |GL(6,2)|. For an actor of
order five, orbit counting and coprime splitting give a moving factor of
order sixteen and a fixed factor of order at most four. Its normalizer
therefore has order dividing 6 * 60 = 360. This excludes the five-core when
sixteen divides the subgroup order. An actor of order thirty-one instead
has a moving factor of order thirty-two and a fixed factor of order at most
two; its normalizer is odd, excluding the thirty-one-core in even order.

The seven-part of |GL(6,2)| is 49. Orbit counting modulo five shows that a
group of order dividing 49 has no automorphism of order five.

These arguments extend the coprime-splitting proofs in
`ElementaryThirtyTwoFiveSevenCores` and `ElementaryThirtyTwoThirtyOneNormalizer`,
which formalize the small linear normalizers in Parrott (1972), p.673.
The dimension-six extensions here use the same elementary counting arguments.
-/

open Subgroup
open scoped IsMulCommutative

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem card_fixed_mul_moving
    {E : Type*} [Group E] [Finite E] [IsMulCommutative E]
    (A : Subgroup (MulAut E)) (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    Nat.card (FixedPoints.subgroup A E) * Nat.card (commutatorAction A E) =
      Nat.card E := by
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := E) (A := A) (Group.isSolvable_of_comm (fun a b : E => mul_comm a b))
      hcop inferInstance
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint (FixedPoints.subgroup A E)
    (commutatorAction A E) (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top, card_top] at hh
  exact hh.symm

private theorem card_normalizer_five_sixteen_dvd_sixty
    {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    (A : Subgroup (MulAut V)) (hA : Nat.card A = 5) :
    Nat.card (normalizer (A : Set (MulAut V))) ∣ 60 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  let f := A.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 4 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Nat.card f.ker ∣ 15 := by
    have hc := card_centralizer_five_dvd_fifteen (V := V) A hA hV
    have heq : Nat.card f.ker = Nat.card (centralizer (A : Set (MulAut V))) := by
      rw [normalizerMonoidHom_ker,
        Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (MulAut V)))).toEquiv]
    rwa [heq]
  have hh := Nat.mul_dvd_mul hker hrange
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  simpa only [hprod] using hh

private theorem core_eq_bot_of_normalizer_obstruction
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (d : ℕ) (hd : d ∣ Nat.card B)
    (p : ℕ) [Fact p.Prime] (hnot : ¬ p ^ 2 ∣ Nat.card G)
    (hnorm : ∀ A : Subgroup G, Nat.card A = p →
      ¬ d ∣ Nat.card (normalizer (A : Set G))) : pCore p B = ⊥ := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := B)).exists_card_eq
  have hdiv : p ^ n ∣ Nat.card G := by
    rw [← hn]
    exact dvd_trans (pCore p B).card_subgroup_dvd_card B.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact hnot (dvd_trans (pow_dvd_pow p hh) hdiv)
  by_cases hz : n = 0
  · apply Subgroup.card_eq_one.mp
    simpa only [hz, pow_zero] using hn
  have hn1 : n = 1 := by omega
  have hcard : Nat.card (pCore p B) = p := by simpa only [hn1, pow_one] using hn
  let A := (pCore p B).map B.subtype
  have hA : Nat.card A = p := by
    rw [card_map_of_injective B.subtype_injective]
    exact hcard
  have hle : B ≤ normalizer (A : Set G) := by
    have hh := (pCore p B).le_normalizer_map B.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, B.range_subtype] using hh
  exact (hnorm A hA (dvd_trans hd (card_dvd_of_le hle))).elim


private theorem dimension_le_six
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) : ∃ n ≤ 6, Nat.card E = 2 ^ n := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  refine ⟨n, ?_, hn⟩
  by_contra! hh
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
  rw [← hn] at hp
  norm_num at hp
  omega

/-- In binary dimension at most six, the automorphism order divides |GL(6,2)|. -/
public theorem card_mulAut_dvd_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) : Nat.card (MulAut E) ∣ 20158709760 := by
  obtain ⟨n, hn, hcard⟩ := dimension_le_six hE
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hcard]
  interval_cases n <;> decide

private theorem prime_fixed_and_moving
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 31)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = p) :
    (Nat.card (FixedPoints.subgroup A E) = 1 ∨
      Nat.card (FixedPoints.subgroup A E) = 2 ∨
      Nat.card (FixedPoints.subgroup A E) = 4) ∧
    Nat.card (commutatorAction A E) = (if p = 5 then 16 else 32) ∧
    (p = 31 → Nat.card (FixedPoints.subgroup A E) ≠ 4) := by
  obtain ⟨n, hn, hcard⟩ := dimension_le_six hE
  let F := FixedPoints.subgroup A E
  have hmod := (IsPGroup.of_card (p := p) (G := A) (n := 1)
    (by simpa using hA)).card_modEq_card_fixedPoints E
  change Nat.card E % p = Nat.card F % p at hmod
  have hdiv : Nat.card F ∣ 2 ^ n := hcard ▸ F.card_subgroup_dvd_card
  obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hproper : Nat.card F ≠ Nat.card E := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq hh
    have hbot : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      exact (show x ∈ F from htop ▸ mem_top x) ⟨a, ha⟩
    rw [hbot, card_bot] at hA
    exact (Fact.out : p.Prime).ne_one hA.symm
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by
    rw [hA, hcard]
    apply Nat.Coprime.pow_right
    rcases hp with rfl | rfl <;> decide
  have hprod := card_fixed_mul_moving A hcop
  change Nat.card F * Nat.card (commutatorAction A E) = Nat.card E at hprod
  change (Nat.card F = 1 ∨ Nat.card F = 2 ∨ Nat.card F = 4) ∧ _ ∧ _
  rw [hkcard, hcard] at hmod hprod hproper
  rw [hkcard]
  rcases hp with rfl | rfl <;>
    interval_cases n <;> interval_cases k <;> norm_num at * <;> omega

/-- Five-subgroup normalizers in binary dimension at most six have order dividing 360. -/
public theorem card_normalizer_five_dvd_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E)) (hA : Nat.card A = 5) :
    Nat.card (normalizer (A : Set (MulAut E))) ∣ 360 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hF, hC, _⟩ := prime_fixed_and_moving hE 5 (Or.inl rfl) A hA
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by
    obtain ⟨n, _, hn⟩ := dimension_le_six hE
    rw [hA, hn]
    exact (show Nat.Coprime 5 2 by decide).pow_right n
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  have hfixed : Nat.card (MulAut (FixedPoints.subgroup A E)) ∣ 6 := by
    rcases hF with hF | hF | hF
    · rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 0 hF]
      decide
    · rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 1 hF]
      decide
    · rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 hF]
      decide
  exact hdiv.trans (Nat.mul_dvd_mul hfixed
    (card_normalizer_five_sixteen_dvd_sixty hC D (hD.trans hA)))

/-- Divisibility by sixteen excludes the five-core in binary dimension at most six. -/
public theorem five_core_eq_bot_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (B : Subgroup (MulAut E)) (hB : 16 ∣ Nat.card B) :
    pCore 5 B = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply core_eq_bot_of_normalizer_obstruction B 16 hB 5
  · intro hh
    have := hh.trans (card_mulAut_dvd_of_elementary_card_le_sixtyfour hE)
    norm_num at this
  · intro A hA hh
    have := hh.trans (card_normalizer_five_dvd_of_elementary_card_le_sixtyfour hE A hA)
    norm_num at this

/-- Thirty-one-subgroup normalizers remain odd in binary dimension at most six. -/
public theorem odd_card_normalizer_thirtyone_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E)) (hA : Nat.card A = 31) :
    Odd (Nat.card (normalizer (A : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨hF, hC, hFne⟩ := prime_fixed_and_moving hE 31 (Or.inr rfl) A hA
  simp only [show ¬ (31 : ℕ) = 5 by decide, if_false] at hC
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by
    obtain ⟨n, _, hn⟩ := dimension_le_six hE
    rw [hA, hn]
    exact (show Nat.Coprime 31 2 by decide).pow_right n
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  have hfixed : Nat.card (MulAut (FixedPoints.subgroup A E)) = 1 := by
    rcases hF with hF | hF | hF
    · rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 0 hF]
      decide
    · rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 1 hF]
      decide
    · exact (hFne rfl hF).elim
  rw [hfixed, one_mul] at hdiv
  exact (odd_card_normalizer_of_elementary_thirtytwo_thirtyone _ hC D
    (hD.trans hA)).of_dvd_nat hdiv

/-- Even order excludes the thirty-one-core in binary dimension at most six. -/
public theorem thirtyone_core_eq_bot_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (B : Subgroup (MulAut E)) (hB : 2 ∣ Nat.card B) :
    pCore 31 B = ⊥ := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  apply core_eq_bot_of_normalizer_obstruction B 2 hB 31
  · intro hh
    have := hh.trans (card_mulAut_dvd_of_elementary_card_le_sixtyfour hE)
    norm_num at this
  · intro A hA
    exact (odd_card_normalizer_thirtyone_of_elementary_card_le_sixtyfour hE A hA).not_two_dvd_nat

/-- A seven-subgroup in binary dimension at most six has no automorphism of order five. -/
public theorem not_five_dvd_card_mulAut_seven_subgroup_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E)) (hA : IsPGroup 7 A) :
    ¬ 5 ∣ Nat.card (MulAut A) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdiv : 7 ^ n ∣ 20158709760 := by
    rw [← hn]
    exact A.card_subgroup_dvd_card.trans
      (card_mulAut_dvd_of_elementary_card_le_sixtyfour hE)
  have hnle : n ≤ 2 := by
    by_contra! hh
    have hbad : 343 ∣ 20158709760 := (pow_dvd_pow 7 hh).trans hdiv
    norm_num at hbad
  intro hfive
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, ha]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P A
  have hmod := hp.card_modEq_card_fixedPoints A
  change Nat.card A % 5 = Nat.card F % 5 at hmod
  have hFdiv : Nat.card F ∣ 7 ^ n := hn ▸ F.card_subgroup_dvd_card
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hFdiv
  have heq : Nat.card F = Nat.card A := by
    rw [hn, hcard] at hmod ⊢
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a, mem_zpowers a⟩
  rw [haone, orderOf_one] at ha
  norm_num at ha

/-- The only possible prime divisors of binary automorphism orders through dimension six. -/
public theorem prime_dvd_card_automorphisms_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (B : Subgroup (MulAut E))
    {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card B) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  have hh : p ∣ 20158709760 := hdiv.trans (B.card_subgroup_dvd_card.trans
    (card_mulAut_dvd_of_elementary_card_le_sixtyfour hE))
  have hfactor : (20158709760 : ℕ) = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by decide
  rw [hfactor] at hh
  rcases hp.dvd_mul.mp hh with hh | hh
  · rcases hp.dvd_mul.mp hh with hh | hh
    · rcases hp.dvd_mul.mp hh with hh | hh
      · rcases hp.dvd_mul.mp hh with hh | hh
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow hh))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow hh)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hh)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh))))
