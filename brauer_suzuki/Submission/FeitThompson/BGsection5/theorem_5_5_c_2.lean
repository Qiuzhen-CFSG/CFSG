/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection5.theorem_5_5_c_1
public import Submission.FeitThompson.BGsection4.theorem_4_16

/-! # Theorem 5.5(c.2) from BG Section 5 -/

private theorem commutatorAction_eq_bot_of_actsTrivially_local
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (htriv : ActsTrivially (A := A) (G := G)) :
    commutatorAction (A := A) (G := G) = ⊥ := by
  rw [commutatorAction_eq_closure, Subgroup.closure_eq_bot_iff]
  intro x hx
  rcases hx with ⟨a, g, rfl⟩
  change g⁻¹ * (a • g) = 1
  simp [ActsTrivially] at htriv
  rw [htriv a g]
  simp

private theorem omega1_eq_centralProduct_left_of_exponent_local
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {R₁ R₂ : Subgroup R}
    (hprod : IsCentralProduct R₁ R₂)
    (hR₁exp : Monoid.exponent R₁ = p)
    (hΩeq :
      (omega₁ (G := R₂) (p := p)).map R₂.subtype = (derivedSubgroup R₁).map R₁.subtype) :
    omega₁ (G := R) (p := p) = R₁ := by
  rcases hprod with ⟨_hR₁norm, _hR₂norm, hcomm12, hsup12⟩
  have hR₁_le_omega : R₁ ≤ omega₁ (G := R) (p := p) := by
    intro y hy
    change y ∈ Subgroup.closure {u : R | u ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    have hy_pow_sub : (⟨y, hy⟩ : R₁) ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) ⟨y, hy⟩
    have hy_pow : y ^ p = 1 := by
      simpa using congrArg R₁.subtype hy_pow_sub
    simpa [pow_one] using hy_pow
  have homega_le_R₁ : omega₁ (G := R) (p := p) ≤ R₁ := by
    rw [omega₁, omega]
    refine (Subgroup.closure_le (K := R₁)).2 ?_
    intro x hx
    have hx_pow : x ^ p = 1 := by simpa [pow_one] using hx
    have hx_sup : x ∈ R₁ ⊔ R₂ := by
      rw [hsup12]
      exact Subgroup.mem_top x
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := R₁) (t := R₂)).1 hx_sup with
      ⟨y, hy, z, hz, hyz⟩
    let yR₁ : R₁ := ⟨y, hy⟩
    let zR₂ : R₂ := ⟨z, hz⟩
    have hy_cent : (z : R) * (y : R) = (y : R) * (z : R) := by
      exact
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := R₁) (H₂ := R₂)).1 hcomm12 hy)
          z hz
    have hy_commute : Commute (y : R) (z : R) := hy_cent.symm
    have hy_pow_sub : yR₁ ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent (↥R₁) ∣ p by simp [hR₁exp]) yR₁
    have hy_pow : (y : R) ^ p = 1 := by
      simpa [yR₁] using congrArg R₁.subtype hy_pow_sub
    have hz_pow : (z : R) ^ p = 1 := by
      have hsplit : ((y : R) * (z : R)) ^ p = (y : R) ^ p * (z : R) ^ p := by
        simpa using hy_commute.mul_pow p
      calc
        (z : R) ^ p = (y : R) ^ p * (z : R) ^ p := by simp [hy_pow]
        _ = ((y : R) * (z : R)) ^ p := by simpa using hsplit.symm
        _ = x ^ p := by simp [hyz]
        _ = 1 := hx_pow
    have hz_pow_sub : zR₂ ^ p = 1 := by
      apply Subtype.ext
      simpa [zR₂] using hz_pow
    have hz_omega : zR₂ ∈ omega₁ (G := R₂) (p := p) := by
      change zR₂ ∈ Subgroup.closure {u : R₂ | u ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [pow_one] using hz_pow_sub
    have hz_map : (z : R) ∈ (omega₁ (G := R₂) (p := p)).map R₂.subtype :=
      Subgroup.mem_map_of_mem R₂.subtype hz_omega
    rw [hΩeq] at hz_map
    rcases Subgroup.mem_map.mp hz_map with ⟨d, hd, hd_eq⟩
    have hz_R₁ : (z : R) ∈ R₁ := by
      rw [← hd_eq]
      exact d.2
    rw [← hyz]
    exact R₁.mul_mem hy hz_R₁
  exact le_antisymm homega_le_R₁ hR₁_le_omega

private theorem actsTrivially_of_prime_card_on_cyclic_pgroup_local
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} [Fact p.Prime]
    (hAcardPrime : (Nat.card A).Prime)
    (hA_not_dvd : ¬ Nat.card A ∣ p * (p - 1))
    (hGp : IsPGroup p G) (hGcyc : IsCyclic G) :
    ActsTrivially (A := A) (G := G) := by
  classical
  by_cases hsub : Subsingleton G
  · intro a g
    exact Subsingleton.elim _ _
  · have hnontriv : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨n, hnpos, hGcard⟩ :=
      (IsPGroup.nontrivial_iff_card (p := p) (G := G) (hG := hGp)).mp hnontriv
    letI : IsCyclic G := hGcyc
    let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
    have hcard_range_dvd_A : Nat.card φ.range ∣ Nat.card A := Subgroup.card_range_dvd φ
    have hA_not_dvd_p : ¬ Nat.card A ∣ p := by
      intro hdiv
      exact hA_not_dvd <| dvd_trans hdiv (dvd_mul_right p (p - 1))
    have hA_not_dvd_pred : ¬ Nat.card A ∣ p - 1 := by
      intro hdiv
      exact hA_not_dvd <| dvd_trans hdiv <| by
        rw [Nat.mul_comm]
        exact dvd_mul_right (p - 1) p
    have hA_not_dvd_pow : ¬ Nat.card A ∣ p ^ (n - 1) := by
      intro hdiv
      exact hA_not_dvd_p (hAcardPrime.dvd_of_dvd_pow hdiv)
    have hA_not_dvd_mulAut : ¬ Nat.card A ∣ Nat.card (MulAut G) := by
      rw [IsCyclic.card_mulAut, hGcard, Nat.totient_prime_pow (Fact.out : Nat.Prime p) hnpos]
      exact hAcardPrime.not_dvd_mul hA_not_dvd_pow hA_not_dvd_pred
    have hrange_card_one : Nat.card φ.range = 1 := by
      rcases hAcardPrime.eq_one_or_self_of_dvd _ hcard_range_dvd_A with h1 | hself
      · exact h1
      · exact False.elim (hA_not_dvd_mulAut (hself ▸ Subgroup.card_subgroup_dvd_card φ.range))
    have hrange_bot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hrange_card_one
    intro a g
    have ha_range : φ a ∈ φ.range := ⟨a, rfl⟩
    have hφa : φ a = 1 := by
      have : φ a ∈ (⊥ : Subgroup (MulAut G)) := by simpa [hrange_bot] using ha_range
      exact Subgroup.mem_bot.mp this
    simpa [φ, MulDistribMulAction.toMulAut_apply] using congrArg (fun f : MulAut G => f g) hφa

public theorem theorem_5_5_c_2
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    {A : Subgroup (MulAut R)} [IsSolvable A] (hoddA : Odd (Nat.card A))
    (hAcardPrime : (Nat.card A).Prime) (hA_not_dvd : ¬ Nat.card A ∣ p * (p - 1))
    (hcomm : commutatorAction A R = ⊤) (hR_nonabelian : ¬ IsMulCommutative R) :
    Nat.card R = p ^ 3 := by
  classical
  have hpR : IsPGroup p R := hnarrow.1
  have hp_ne_Acard : p ≠ Nat.card A := by
    intro hEq
    apply hA_not_dvd
    rw [← hEq]
    exact dvd_mul_right p (p - 1)
  have hcop : Nat.Coprime p (Nat.card A) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 fun hp_dvd =>
      hp_ne_Acard ((hAcardPrime.dvd_iff_eq (Fact.out : Nat.Prime p).ne_one).1 hp_dvd).symm
  have hrank : groupRank R ≤ 2 := by
    by_contra hrank
    have hR : 3 ≤ groupRank R := by omega
    have hA_nontrivial : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hAcardPrime.one_lt
    obtain ⟨a, ha_ne_one⟩ := exists_ne (1 : A)
    have hza_top : Subgroup.zpowers a = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one_local hAcardPrime ha_ne_one
    have horder_eq_card : orderOf a = Nat.card A := by
      calc
        orderOf a = Nat.card (Subgroup.zpowers a) := by rw [← Nat.card_zpowers]
        _ = Nat.card A := by simp [hza_top]
    have hcop_order : Nat.Coprime p (orderOf (a : A)) := by
      rw [horder_eq_card]
      exact hcop
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
    exact hA_not_dvd <|
      dvd_trans hcard_dvd_pred
        (by
          rw [Nat.mul_comm]
          exact dvd_mul_right (p - 1) p)
  letI : Fact (IsPGroup p R) := ⟨hpR⟩
  have hR_nontrivial : Nontrivial R := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hsub
    letI : Subsingleton R := hsub
    letI : IsMulCommutative R := {
      is_comm := {
        comm a b := by
          have ha : a = 1 := Subsingleton.eq_one a
          have hb : b = 1 := Subsingleton.eq_one b
          rw [ha, hb]
      }
    }
    exact hR_nonabelian inferInstance
  letI : Nontrivial R := hR_nontrivial
  obtain ⟨_hpgt, h416⟩ := theorem_4_16
    (R := R) (A := A) hpodd hcop hrank hcomm hoddA
  rcases h416 with hRcomm | ⟨R₁, R₂, hprod, hR₁card, hR₁exp, hR₁_noncomm, hR₂cyc, hΩeq⟩
  · exact False.elim (hR_nonabelian hRcomm)
  · let Ω : Subgroup R := omega₁ (G := R) (p := p)
    letI : R₁.Normal := hprod.1
    letI : R₂.Normal := hprod.2.1
    letI : Ω.Characteristic := by
      simpa [Ω] using (omega₁_characteristic (G := R) (p := p))
    have hΩ_eq_R₁ : Ω = R₁ :=
      omega1_eq_centralProduct_left_of_exponent_local
        (p := p) hprod hR₁exp hΩeq
    have hquot_cyc_R₁ : IsCyclic (R ⧸ R₁) :=
      quotient_isCyclic_of_sup_cyclic_right
        (R := R) (R₁ := R₁) (R₂ := R₂) hprod.2.2.2 hR₂cyc
    have hquot_cyc : IsCyclic (R ⧸ Ω) := by
      let e : R ⧸ R₁ ≃* R ⧸ Ω := QuotientGroup.quotientMulEquivOfEq hΩ_eq_R₁.symm
      exact (e.isCyclic).1 hquot_cyc_R₁
    have hΩinv : IsInvariantSubgroup A R Ω := isInvariant_of_characteristic (A := A) (G := R) Ω
    letI : Ω.Normal := inferInstance
    letI : MulAction.QuotientAction A Ω := quotientAction_of_isInvariant (A := A) Ω hΩinv
    letI : MulDistribMulAction A (R ⧸ Ω) :=
      quotientMulDistribMulAction (A := A) (G := R) Ω hΩinv
    have hquot_p : IsPGroup p (R ⧸ Ω) := hpR.to_quotient Ω
    have hquot_triv : ActsTrivially (A := A) (G := R ⧸ Ω) :=
      actsTrivially_of_prime_card_on_cyclic_pgroup_local
        (A := A) (G := R ⧸ Ω) (p := p) hAcardPrime hA_not_dvd hquot_p hquot_cyc
    have hcomm_le_Ω : commutatorAction (A := A) (G := R) ≤ Ω := by
      refine
        commutatorAction_le_of_actsTrivially_quotient
          (G := R) (A := A) (N := Ω) ?_ hquot_triv
      intro a g
      exact (MulAction.Quotient.smul_coe (H := Ω) a g).symm
    have hΩ_top : Ω = ⊤ := by
      have htop_le_Ω : (⊤ : Subgroup R) ≤ Ω := by
        simpa [hcomm] using hcomm_le_Ω
      exact le_antisymm le_top htop_le_Ω
    have hR₁_top : R₁ = ⊤ := by
      calc
        R₁ = Ω := hΩ_eq_R₁.symm
        _ = ⊤ := hΩ_top
    simpa [hR₁_top] using hR₁card
