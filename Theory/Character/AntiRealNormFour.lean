module

public import Theory.Character.AntiRealCoefficients

import Mathlib.Tactic

/-!
# Anti-real generalized characters of norm four

An anti-real generalized character of squared norm four has exactly four
irreducible constituents. They form two distinct complex-conjugate pairs, with
coefficients `1, -1, 1, -1`.

In a complete irreducible basis the coefficients are integers, and conjugation
negates them. Each nonzero coefficient therefore contributes twice its square
to the norm, forcing its absolute value to be one. The four-element support
then splits into the required two pairs.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp. 72–73, before equation (10).
-/

open scoped BigOperators

private theorem norm_four_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (c : ι → ι) (hc : Function.Involutive c)
    (hneg : ∀ i, a (c i) = -a i) (hnorm : ∑ i, a i * a i = 4) :
    ∃ i j, a i = 1 ∧ a j = 1 ∧ i ≠ j ∧
      (Finset.univ.filter fun k => a k ≠ 0) = {i, c i, j, c j} := by
  classical
  have hsign : ∀ i, a i ≠ 0 → a i = 1 ∨ a i = -1 := by
    intro i hi
    have hne : i ≠ c i := by
      intro he
      have := hneg i
      rw [← he] at this
      omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, c i} : Finset ι))
      (fun k _ _ => mul_self_nonneg (a k))
    rw [Finset.sum_pair hne, hneg, hnorm] at hle
    have hbound : a i * a i ≤ 2 := by nlinarith
    have hlow : -1 ≤ a i := by nlinarith
    have hhigh : a i ≤ 1 := by nlinarith
    omega
  let S := Finset.univ.filter fun k => a k ≠ 0
  have hmem (i : ι) : i ∈ S ↔ a i ≠ 0 := by simp [S]
  have hsum : ∑ i ∈ S, a i * a i = 4 := by
    rw [← hnorm]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : a i = 0 := by simpa [S] using hi
    simp [this]
  have hcard : S.card = 4 := by
    have he : (S.card : ℤ) = 4 := by
      calc
        (S.card : ℤ) = ∑ _i ∈ S, (1 : ℤ) := by simp
        _ = ∑ i ∈ S, a i * a i := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases hsign i ((hmem i).mp hi) with h | h <;> simp [h]
        _ = 4 := hsum
    exact_mod_cast he
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨i, hi⟩ : ∃ i, a i = 1 := by
    rcases hsign k ((hmem k).mp hk) with h | h
    · exact ⟨k, h⟩
    · exact ⟨c k, by rw [hneg, h]; norm_num⟩
  have hci : a (c i) = -1 := by rw [hneg, hi]
  have houtside : ∃ k ∈ S, k ∉ ({i, c i} : Finset ι) := by
    by_contra h
    have hsub : S ⊆ {i, c i} := by
      intro k hk
      by_contra hn
      exact h ⟨k, hk, hn⟩
    have := Finset.card_le_card hsub
    have : ({i, c i} : Finset ι).card ≤ 2 := by
      calc
        _ ≤ ({c i} : Finset ι).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  obtain ⟨k, hk, hkout⟩ := houtside
  have hki : k ≠ i := fun h => hkout (by simp [h])
  have hkci : k ≠ c i := fun h => hkout (by simp [h])
  obtain ⟨j, hj, hji⟩ : ∃ j, a j = 1 ∧ j ≠ i := by
    rcases hsign k ((hmem k).mp hk) with h | h
    · exact ⟨k, h, hki⟩
    · refine ⟨c k, by rw [hneg, h]; norm_num, ?_⟩
      intro he
      apply hkci
      simpa only [hc k] using congrArg c he
  have hcj : a (c j) = -1 := by rw [hneg, hj]
  have hi_ci : i ≠ c i := by intro h; rw [h] at hi; omega
  have hi_cj : i ≠ c j := by intro h; rw [h] at hi; omega
  have hci_j : c i ≠ j := by intro h; rw [h] at hci; omega
  have hj_cj : j ≠ c j := by intro h; rw [h] at hj; omega
  have hci_cj : c i ≠ c j := fun h => hji (hc.injective h).symm
  refine ⟨i, j, hi, hj, hji.symm, ?_⟩
  change S = _
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [hmem, hi, hj, hci, hcj]
  · simp [hcard, hi_ci, hji.symm, hi_cj, hci_j, hci_cj, hj_cj]

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- An anti-real generalized character of norm four consists of two distinct
conjugate pairs, with coefficients `1, -1, 1, -1`. -/
theorem IsGeneralizedCharacter.exists_four_irreducibles_of_antiReal_norm_four
    {Θ : ClassFunction G} (hΘ : IsGeneralizedCharacter Θ)
    (hnorm : scalarProduct G Θ Θ = 4)
    (hanti : ∀ g, star (Θ g) = -Θ g) :
    ∃ q : Fin 4 → ClassFunction G,
      (∀ i, IsIrreducibleCharacter (q i)) ∧ Function.Injective q ∧
      Θ = q 0 - q 1 + q 2 - q 3 ∧
      (∀ i, scalarProduct G Θ (q i) = (![1, -1, 1, -1] : Fin 4 → ℂ) i) ∧
      q 1 = (fun g => star (q 0 g)) ∧ q 3 = (fun g => star (q 2 g)) := by
  classical
  obtain ⟨ι, hι, ξ, hξ, _b, _hb⟩ := irreducible_characters_form_basis (G := G)
  let : Fintype ι := hι
  let μ : ι → ClassFunction G := fun i => ofConjClassFunction (ξ i)
  have hirr : ∀ i, IsIrreducibleCharacter (μ i) := by
    intro i
    obtain ⟨⟨n, ρ, he⟩, hn⟩ := hξ.1 i
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · rwa [he] at hn
    · change ofConjClassFunction (ξ i) = ρ.character
      rw [he, ofConjClassFunction_characterClassFunction]
  have hinj : Function.Injective μ := by
    intro i j he
    apply hξ.2.2
    ext t
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep t
    exact congrFun he g
  have hcomplete : ∀ χ, IsIrreducibleCharacter χ → ∃ i, μ i = χ := by
    rintro χ ⟨n, ρ, hρ, rfl⟩
    obtain ⟨i, hi⟩ := hξ.2.1 (characterClassFunction ρ)
      ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
    exact ⟨i, congrArg ofConjClassFunction hi⟩
  have hex : ∀ i, ∃ j, μ j = fun g => star (μ i g) := by
    intro i
    exact hcomplete _ ((hirr i).comp_ringEquiv (starRingAut : ℂ ≃+* ℂ))
  choose c hconj using hex
  have hc : Function.Involutive c := by
    intro i
    apply hinj
    ext g
    simp only [congrFun (hconj (c i)) g, congrFun (hconj i) g, star_star]
  choose a ha using fun i => hΘ.scalarProduct_irreducible_int (hirr i)
  have hneg : ∀ i, a (c i) = -a i := by
    intro i
    have h := hΘ.scalarProduct_conjugate_of_antiReal hanti (hirr i)
    rw [← hconj, ha, ha] at h
    exact_mod_cast h
  have hclass : IsClassFunction Θ := by
    obtain ⟨χ, ψ, ⟨n, ρ, rfl⟩, ⟨m, σ, rfl⟩, rfl⟩ := hΘ
    intro x g
    simp only [Pi.sub_apply, Representation.char_conj]
  let Φ := toConjClassFunction Θ hclass
  have hinner (i : ι) : classFunctionInner Φ (ξ i) = (a i : ℂ) := by
    exact (classFunctionInner_toConjClassFunction_right Θ hclass (ξ i)).trans (ha i)
  have hreverse (i : ι) : classFunctionInner (ξ i) Φ = (a i : ℂ) := by
    change scalarProduct G (μ i) Θ = (a i : ℂ)
    rw [← scalarProduct_conj, ha, star_intCast]
  have hexpand : (∑ i, (a i : ℂ) • ξ i) = Φ := by
    simpa only [hinner] using completeFamily_sum_inner_smul_eq hξ Φ
  have hsum : ∑ i, a i * a i = 4 := by
    have h := congrArg (fun f => classFunctionInner f Φ) hexpand
    rw [classFunctionInner_sum_left] at h
    simp only [hreverse, smul_eq_mul] at h
    change ∑ i, (a i : ℂ) * (a i : ℂ) = scalarProduct G Θ Θ at h
    rw [hnorm] at h
    exact_mod_cast h
  obtain ⟨i, j, hi, hj, hij, hs⟩ := norm_four_pairs a c hc hneg hsum
  have hci : a (c i) = -1 := by rw [hneg, hi]
  have hcj : a (c j) = -1 := by rw [hneg, hj]
  have hi_ci : i ≠ c i := by intro h; rw [h] at hi; omega
  have hi_cj : i ≠ c j := by intro h; rw [h] at hi; omega
  have hci_j : c i ≠ j := by intro h; rw [h] at hci; omega
  have hj_cj : j ≠ c j := by intro h; rw [h] at hj; omega
  have hci_cj : c i ≠ c j := fun h => hij (hc.injective h)
  let q : Fin 4 → ClassFunction G := ![μ i, μ (c i), μ j, μ (c j)]
  refine ⟨q, ?_, ?_, ?_, ?_, hconj i, hconj j⟩
  · intro k
    fin_cases k <;> exact hirr _
  · intro k l he
    fin_cases k <;> fin_cases l <;>
      simp [q, hinj.eq_iff, hi_ci, hi_ci.symm, hij, hij.symm, hi_cj, hi_cj.symm,
        hci_j, hci_j.symm, hci_cj, hci_cj.symm, hj_cj, hj_cj.symm] at he ⊢
  · ext g
    have heval : Θ g = ∑ k, (a k : ℂ) * μ k g := by
      simpa [μ, Φ, ofConjClassFunction, toConjClassFunction_apply, smul_eq_mul] using
        (congrFun hexpand (ConjClasses.mk g)).symm
    rw [heval]
    have hrestrict : (∑ k, (a k : ℂ) * μ k g) =
        ∑ k ∈ Finset.univ.filter (fun k => a k ≠ 0), (a k : ℂ) * μ k g := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have : a k = 0 := by simpa using hk
      simp [this]
    rw [hrestrict, hs]
    simp [q, hi_ci, hij, hi_cj, hci_j, hci_cj, hj_cj, hi, hci, hj, hcj]
    ring
  · intro k
    fin_cases k <;> simp [q, ha, hi, hci, hj, hcj]
