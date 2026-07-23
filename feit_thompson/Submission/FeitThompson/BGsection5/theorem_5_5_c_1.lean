/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection5.theorem_5_5_b
public import FeitThompson.BGsection4.lemma_4_7
public import FeitThompson.BGsection4.lemma_4_14

/-! # Theorem 5.5(c.1) from BG Section 5 -/

public theorem theorem_5_5_c_1
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    {A : Subgroup (MulAut R)} [IsSolvable A] (hoddA : Odd (Nat.card A))
    (hAcardPrime : (Nat.card A).Prime) (hA_not_dvd : ¬ Nat.card A ∣ p * (p - 1)) :
    Nat.card A ∣ (p + 1) / 2 := by
  classical
  have hpR : IsPGroup p R := hnarrow.1
  by_cases hrank : groupRank R ≤ 2
  · letI : Fact (IsPGroup p R) := ⟨hpR⟩
    have hA3empty : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ := by
      have h47 := (lemma_4_7 (R := R) (p := p) hpodd hpR)
      exact (h47.mpr hrank)
    have hp_ne_Acard : p ≠ Nat.card A := by
      intro hEq
      apply hA_not_dvd
      rw [← hEq]
      exact dvd_mul_right p (p - 1)
    have hAcard_ne_p : Nat.card A ≠ p := by
      intro hEq
      exact hp_ne_Acard hEq.symm
    letI : Fact (Nat.Prime (Nat.card A)) := ⟨hAcardPrime⟩
    have hA_dvd_mulAut : Nat.card A ∣ Nat.card (MulAut R) :=
      dvd_trans (Subgroup.card_subgroup_dvd_card A) (dvd_rfl)
    rcases lemma_4_14 (R := R) (p := p) (q := Nat.card A) hpodd
        (hA3 := hA3empty) hA_dvd_mulAut hAcard_ne_p with hdiv | hdiv
    · exact hdiv
    · exfalso
      apply hA_not_dvd
      have hhalf_dvd : (p - 1) / 2 ∣ p - 1 := by
        exact Nat.div_dvd_of_dvd (even_iff_two_dvd.mp ((Fact.out : Nat.Prime p).even_sub_one hpodd))
      exact dvd_trans hdiv <| dvd_trans hhalf_dvd <| by
        rw [Nat.mul_comm]
        exact dvd_mul_right (p - 1) p
  · have hR : 3 ≤ groupRank R := by omega
    have hA_nontrivial : Nontrivial A := by
      exact Finite.one_lt_card_iff_nontrivial.mp hAcardPrime.one_lt
    obtain ⟨a, ha_ne_one⟩ := exists_ne (1 : A)
    have hza_top : Subgroup.zpowers a = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one_local hAcardPrime ha_ne_one
    have horder_eq_card : orderOf a = Nat.card A := by
      calc
        orderOf a = Nat.card (Subgroup.zpowers a) := by
          rw [← Nat.card_zpowers]
        _ = Nat.card A := by simp [hza_top]
    have hcop_order : Nat.Coprime p (orderOf (a : A)) := by
      rw [horder_eq_card]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 fun hp_dvd =>
        hp_ne_Acard ((hAcardPrime.dvd_iff_eq (Fact.out : Nat.Prime p).ne_one).1 hp_dvd).symm
    have horder_dvd : orderOf ((a : A) : MulAut R) ∣ p - 1 := by
      have hcop_order' : Nat.Coprime p (orderOf ((a : A) : MulAut R)) := by
        simpa [Subgroup.orderOf_coe] using hcop_order
      simpa using theorem_5_5_b
        (p := p) hpodd (R := R) hnarrow hR (A := A) hoddA ((a : A) : MulAut R) a.2 hcop_order'
    have horder_eq_card_coe : orderOf ((a : A) : MulAut R) = Nat.card A := by
      simpa [Subgroup.orderOf_coe] using horder_eq_card
    have hcard_dvd_pred : Nat.card A ∣ p - 1 := by
      rw [horder_eq_card_coe] at horder_dvd
      exact horder_dvd
    exact False.elim <| hA_not_dvd (dvd_trans hcard_dvd_pred <| by
      rw [Nat.mul_comm]
      exact dvd_mul_right (p - 1) p)
where
  hp_ne_Acard : p ≠ Nat.card A := by
    intro hEq
    apply hA_not_dvd
    rw [← hEq]
    exact dvd_mul_right p (p - 1)
