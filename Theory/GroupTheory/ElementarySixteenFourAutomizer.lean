module

public import Theory.GroupAction.CommonFixedFourOddAction
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# A common fixed four in a solvable automizer of an elementary sixteen

If a Sylow two-subgroup P of a solvable subgroup K of Aut(E) is elementary
of order four, and each nonidentity element of P has fixed subgroup F,
then every element of K preserves F. In particular this holds when E has
order sixteen and F has order four, as in the stated application.

The common-fixed-subgroup action lemma makes P centralize every odd prime
core. If the two-core were trivial, the Fitting subgroup would have odd
order and would be centralized by P. Fitting self-centralization would
then put P in an odd-order group, a contradiction. The nontrivial normal
two-core lies in P. Conjugating any of its nonidentity elements now
transports F to itself.

The two-core conclusion needs no dimension bound on E. The final theorem
retains the elementary-sixteen and fixed-four hypotheses of the local
fusion application in MacWilliams (1970), DOI
10.1090/S0002-9947-1970-0276324-3. No subgroup enumeration or classification
of GL(4,2) is used.
-/

open Subgroup

private theorem fixed_map_eq_of_nontrivial_normal_subgroup
    {E : Type*} [Group E] [Finite E]
    (K : Subgroup (MulAut E)) (A : Subgroup K) (F : Subgroup E)
    (hfixed : ∀ a : A, a ≠ 1 → ∀ x : E,
      (((a : K) : MulAut E) x = x ↔ x ∈ F))
    (Q : Subgroup K) [Q.Normal] (hQA : Q ≤ A) (hQ : Q ≠ ⊥)
    (k : K) : F.map (k : MulAut E).toMonoidHom = F := by
  have hex : ∃ a : K, a ∈ Q ∧ a ≠ 1 := by
    by_contra! hn
    apply hQ
    exact eq_bot_iff.mpr hn
  obtain ⟨a, ha, hane⟩ := hex
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    apply (hfixed ⟨a, hQA ha⟩ (fun hh => hane (congrArg Subtype.val hh)) _).mp
    have hb : k⁻¹ * a * k ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem a ha k⁻¹
    have hbne : k⁻¹ * a * k ≠ 1 := by
      intro hh
      apply hane
      have := congrArg (fun z : K => k * z * k⁻¹) hh
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_one,
        mul_inv_cancel] using this
    have hfix : (k⁻¹ * a * k) • x = x :=
      (hfixed ⟨k⁻¹ * a * k, hQA hb⟩
        (fun hh => hbne (congrArg Subtype.val hh)) x).mpr hx
    change a • (k • x) = k • x
    calc
      a • (k • x) = k • ((k⁻¹ * a * k) • x) := by
        simp only [← mul_smul, mul_inv_cancel_left, mul_assoc]
      _ = k • x := congrArg (fun y : E => k • y) hfix
  · exact (card_map_of_injective (k : MulAut E).injective).ge

private theorem twoCore_ne_bot_of_centralizes_odd_cores
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hcentral : ∀ q : ℕ, q.Prime → q ≠ 2 →
      A ≤ centralizer (pCore q G : Set G)) : pCore 2 G ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcore
  have hfit : fittingSubgroup G ≤ pPrimeCore 2 G := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun prime => ?_
    by_cases heq : prime.val.val = 2
    · rw [heq, hcore]
      exact bot_le
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨exponent, hcard⟩ :=
        (pCore_isPGroup (p := prime.val.val) (G := G)).exists_card_eq
      rw [hcard]
      exact ((Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors prime.val.property)).mpr (Ne.symm heq)).pow_right _
  have hcentralFit : A ≤ centralizer (fittingSubgroup G : Set G) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro prime
    by_cases heq : prime.val.val = 2
    · rw [heq, hcore]
      intro a ha b hb
      have hb1 : b = 1 := hb
      simp [hb1]
    · exact hcentral _ (Nat.prime_of_mem_primeFactors prime.val.property) heq
  have hle : A ≤ pPrimeCore 2 G :=
    hcentralFit.trans ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      inferInstance).trans hfit)
  have hcop : Nat.Coprime 2 (Nat.card A) :=
    pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hcard : Nat.card A = 1 := by
    rw [hn] at hcop ⊢
    rcases n with _ | n
    · rfl
    · have hd : 2 ∣ 2 ^ (n + 1) := dvd_pow_self 2 (by omega)
      have := hcop.eq_one_of_dvd hd
      norm_num at this
  exact hne (card_eq_one.mp hcard)


/-- A solvable faithful binary automizer containing an elementary four with
identical nonidentity fixed subgroups has nontrivial two-core. -/
public theorem twoCore_ne_bot_of_solvable_common_fixed_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (K : Subgroup (MulAut E)) [Group.IsSolvable K]
    (A : Subgroup K) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (F : Subgroup E)
    (hfixed : ∀ a : A, a ≠ 1 → ∀ x : E,
      (((a : K) : MulAut E) x = x ↔ x ∈ F)) : pCore 2 K ≠ ⊥ := by
  have hne : A ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hA
    omega
  apply twoCore_ne_bot_of_centralizes_odd_cores A (IsElementaryAbelian.isPGroup 2 A) hne
  intro q hq hq2
  let : Fact q.Prime := ⟨hq⟩
  have hodd : Odd (Nat.card (pCore q K)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q) (G := K)).exists_card_eq
    rw [hn]
    exact (hq.odd_of_ne_two hq2).pow
  exact odd_normal_centralizes_of_common_fixed_four K A hA F hfixed (pCore q K) hodd

/-- The common fixed four of this Sylow four is invariant under the entire
solvable automorphism subgroup of the elementary sixteen. -/
public theorem map_eq_of_solvable_aut16_common_fixed_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (_hE : Nat.card E = 16) (K : Subgroup (MulAut E)) [Group.IsSolvable K]
    (P : Sylow 2 K) [IsElementaryAbelian 2 P] (hP : Nat.card P = 4)
    (F : Subgroup E) (_hF : Nat.card F = 4)
    (hfixed : ∀ a : P, a ≠ 1 → ∀ x : E,
      (((a : K) : MulAut E) x = x ↔ x ∈ F)) :
    ∀ k : K, F.map (k : MulAut E).toMonoidHom = F := by
  intro k
  exact fixed_map_eq_of_nontrivial_normal_subgroup K (P : Subgroup K) F hfixed
    (pCore 2 K) (fitting_pCore_le_sylow P)
    (twoCore_ne_bot_of_solvable_common_fixed_four K (P : Subgroup K) hP F hfixed) k
