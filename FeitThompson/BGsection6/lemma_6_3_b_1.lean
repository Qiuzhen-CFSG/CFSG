/-
Authors: OpenAI, Yusen Tang
-/

module

public import FeitThompson.BGsection6.lemma_6_3_a_2

open scoped MatrixGroups Pointwise TensorProduct commutatorElement IsMulCommutative

/-! # lemma_6_3_b_1 from BG Section 6 -/

public theorem lemma_6_3_b_1
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hdn : Group.IsNilpotent (derivedSubgroup G))
    (hip : (Nat.card (G ⧸ derivedSubgroup G)).Prime) :
    ∃ π : Set Nat.Primes, IsHallSubgroup π (derivedSubgroup G) := by
  classical
  let D : Subgroup G := derivedSubgroup G
  let p : ℕ := Nat.card (G ⧸ D)
  have hp_prime : Nat.Prime p := by
    simpa [p, D] using hip
  letI : Fact p.Prime := ⟨hp_prime⟩
  have hcoreQbot : pPrimeCore p (G ⧸ D) = ⊥ := by
    apply (pPrimeCore_eq_bot_iff (p := p) (G := G ⧸ D)).2
    intro K hK_normal hK_coprime
    have hK_dvd_p : Nat.card K ∣ p := by
      simpa [p] using (Subgroup.card_subgroup_dvd_card K)
    have hK_card_one : Nat.card K = 1 :=
      Nat.eq_one_of_dvd_coprimes hK_coprime hK_dvd_p (dvd_rfl : Nat.card K ∣ Nat.card K)
    exact (Subgroup.card_eq_one (H := K)).1 hK_card_one
  let N : Subgroup G := pPrimeCore p G
  letI : N.Normal := by
    dsimp [N]
    exact pPrimeCore_normal
  have hN_le_D : N ≤ D := pPrimeCore_le_of_quotient_eq_bot (G := G) (p := p) (N := D) hcoreQbot
  let q : G →* (G ⧸ N) := QuotientGroup.mk' N
  let Dq : Subgroup (G ⧸ N) := D.map q
  have hDq_normal : Dq.Normal := by
    dsimp [Dq, q]
    exact Subgroup.Normal.map (inferInstance : D.Normal) (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  let eDq : (↥D ⧸ N.subgroupOf D) ≃* Dq := by
    simpa [Dq, q] using (quotientSubgroupRangeEquiv D N)
  have hDquot_nil : Group.IsNilpotent (↥D ⧸ N.subgroupOf D) := by
    letI : Group.IsNilpotent ↥D := hdn
    infer_instance
  have hDq_nil : Group.IsNilpotent ↥Dq := by
    exact Group.nilpotent_of_surjective eDq.toMonoidHom eDq.surjective
  have hcoreQN : pPrimeCore p (G ⧸ N) = ⊥ := by
    simpa [N] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hDq_p : IsPGroup p Dq :=
    isPGroup_of_nilpotent_normal (G := G ⧸ N) (p := p) Dq hDq_normal hDq_nil hcoreQN
  have hq_top : (⊤ : Subgroup G).map q = ⊤ := by
    exact Subgroup.map_top_of_surjective (f := q) (QuotientGroup.mk'_surjective N)
  have hderivedQ : Dq = derivedSubgroup (G ⧸ N) := by
    calc
      Dq = D.map q := rfl
      _ = derivedSubgroup (G ⧸ N) := by
        simpa [D, derivedSubgroup, commutator, hq_top] using
          (Subgroup.map_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G)) q)
  have hQab_card : Nat.card ((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N)) = p := by
    calc
      Nat.card ((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N))
          = Nat.card ((G ⧸ N) ⧸ Dq) := by rw [← hderivedQ]
      _ = Nat.card (G ⧸ D) := by
        exact Nat.card_congr
          (QuotientGroup.quotientQuotientEquivQuotient (N := N) (M := D) hN_le_D).toEquiv
      _ = p := by rfl
  have hQab_card_Dq : Nat.card ((G ⧸ N) ⧸ Dq) = p := by
    simpa [hderivedQ] using hQab_card
  obtain ⟨n, hn⟩ := hDq_p.exists_card_eq
  have hQ_p : IsPGroup p (G ⧸ N) := by
    apply IsPGroup.of_card (p := p) (n := n + 1)
    calc
      Nat.card (G ⧸ N) = Nat.card ((G ⧸ N) ⧸ Dq) * Nat.card Dq := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup Dq)
      _ = p * p ^ n := by rw [hQab_card_Dq, hn]
      _ = p ^ (n + 1) := by rw [pow_succ', Nat.mul_comm]
  have hQ_card_ne_one : Nat.card (G ⧸ N) ≠ 1 := by
    intro hQ_card_one
    have hquot_dvd : Nat.card ((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N)) ∣ Nat.card (G ⧸ N) :=
      Subgroup.card_quotient_dvd_card (s := derivedSubgroup (G ⧸ N))
    have hquot_one : Nat.card ((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N)) = 1 :=
      Nat.eq_one_of_dvd_one (hQ_card_one ▸ hquot_dvd)
    exact hp_prime.ne_one (hQab_card.symm.trans hquot_one)
  letI : Fact (IsPGroup p (G ⧸ N)) := ⟨hQ_p⟩
  let Φ : Subgroup (G ⧸ N) := frattini (G ⧸ N)
  have hΦ_eq :
      Φ =
        Subgroup.closure
          (((derivedSubgroup (G ⧸ N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪
            Set.range (fun x : G ⧸ N => x ^ p)) := by
    simpa [Φ, derivedSubgroup, derivedSeries_one, commutator] using
      (frattini_eq_closure_commutator_union_powers (R := G ⧸ N) (p := p))
  have hcomm_le_Φ : derivedSubgroup (G ⧸ N) ≤ Φ := by
    intro x hx
    rw [hΦ_eq]
    exact Subgroup.subset_closure (Or.inl hx)
  have hΦ_ne_top : Φ ≠ ⊤ := by
    intro hΦ_top
    have hbot_top : (⊥ : Subgroup (G ⧸ N)) = ⊤ := by
      apply lemma_1_7_a (R := G ⧸ N) (p := p) (H := (⊥ : Subgroup (G ⧸ N)))
      rw [bot_sup_eq]
      exact hΦ_top
    have hQ_card_one : Nat.card (G ⧸ N) = 1 := by
      simpa [hbot_top] using (Subgroup.card_bot (G := G ⧸ N))
    exact hQ_card_ne_one hQ_card_one
  have hQPhi_dvd_p : Nat.card ((G ⧸ N) ⧸ Φ) ∣ p := by
    let Φbar : Subgroup (((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N))) :=
      Φ.map (QuotientGroup.mk' (derivedSubgroup (G ⧸ N)))
    have hdvd :
        Nat.card ((((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N)) ⧸ Φbar)) ∣
          Nat.card ((G ⧸ N) ⧸ derivedSubgroup (G ⧸ N)) :=
      Subgroup.card_quotient_dvd_card (s := Φbar)
    rw [hQab_card] at hdvd
    exact (Nat.card_congr
      (QuotientGroup.quotientQuotientEquivQuotient
        (N := derivedSubgroup (G ⧸ N)) (M := Φ) hcomm_le_Φ).toEquiv) ▸ hdvd
  have hQPhi_card_ne_one : Nat.card ((G ⧸ N) ⧸ Φ) ≠ 1 := by
    intro hQPhi_one
    have hsub : Subsingleton ((G ⧸ N) ⧸ Φ) := (Nat.card_eq_one_iff_unique.mp hQPhi_one).1
    exact hΦ_ne_top ((QuotientGroup.subsingleton_iff (N := Φ)).1 hsub)
  have hQPhi_card : Nat.card ((G ⧸ N) ⧸ Φ) = p := by
    rcases (Nat.dvd_prime hp_prime).1 hQPhi_dvd_p with hone | hp
    · exact False.elim (hQPhi_card_ne_one hone)
    · exact hp
  have hQPhi_cyclic : IsCyclic ((G ⧸ N) ⧸ Φ) := isCyclic_of_prime_card hQPhi_card
  obtain ⟨xbar, hxbar⟩ := IsCyclic.exists_generator (α := (G ⧸ N) ⧸ Φ)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Φ xbar
  let H : Subgroup (G ⧸ N) := Subgroup.zpowers x
  have hHmap_top : H.map (QuotientGroup.mk' Φ) = ⊤ := by
    apply top_unique
    intro y hy
    rw [show H.map (QuotientGroup.mk' Φ) = Subgroup.zpowers (QuotientGroup.mk' Φ x) by
      simp [H]]
    exact hxbar y
  have hHsup : H ⊔ Φ = ⊤ := by
    apply top_unique
    intro y hy
    have hybar : QuotientGroup.mk' Φ y ∈ H.map (QuotientGroup.mk' Φ) := by
      simp [hHmap_top]
    rcases Subgroup.mem_map.mp hybar with ⟨h, hhH, hhq⟩
    have hzΦ : h⁻¹ * y ∈ Φ := by
      apply (QuotientGroup.eq_one_iff (N := Φ) (x := h⁻¹ * y)).1
      calc
        QuotientGroup.mk' Φ (h⁻¹ * y)
            = (QuotientGroup.mk' Φ h)⁻¹ * QuotientGroup.mk' Φ y := by simp
        _ = 1 := by simp [hhq]
    exact (Subgroup.mem_sup_of_normal_right (s := H) (t := Φ) (x := y)).2
      ⟨h, hhH, h⁻¹ * y, hzΦ, by simp⟩
  have hH_top : H = ⊤ := lemma_1_7_a (R := G ⧸ N) (p := p) (H := H) hHsup
  have hQ_cyclic : IsCyclic (G ⧸ N) := by
    exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, by simpa [H] using hH_top⟩
  letI : IsCyclic (G ⧸ N) := hQ_cyclic
  letI : IsMulCommutative (G ⧸ N) := IsCyclic.isMulCommutative
  letI : CommGroup (G ⧸ N) := IsMulCommutative.instCommGroup
  have hderivedQ_bot : derivedSubgroup (G ⧸ N) = ⊥ := by
    have htop_cent :
        (⊤ : Subgroup (G ⧸ N)) ≤
          Subgroup.centralizer (((⊤ : Subgroup (G ⧸ N)) : Set (G ⧸ N))) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact mul_comm b a
    have hcomm_bot :
        ⁅(⊤ : Subgroup (G ⧸ N)), (⊤ : Subgroup (G ⧸ N))⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).2 htop_cent
    simpa [derivedSubgroup, commutator] using hcomm_bot
  have hDq_bot : Dq = ⊥ := by
    exact hderivedQ.trans hderivedQ_bot
  have hD_le_N : D ≤ N := by
    simpa [Dq, q, QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff (f := q) (H := D)).1 hDq_bot
  have hD_eq_N : D = N := le_antisymm hD_le_N hN_le_D
  let π : Set Nat.Primes := {q | q.val ∣ Nat.card D}
  have hcop_index : Nat.Coprime (Nat.card D) D.index := by
    have hcop : Nat.Coprime p (Nat.card D) := by
      rw [hD_eq_N]
      exact pPrimeCore_coprime_card
    simpa [p, D, Subgroup.index_eq_card] using hcop.symm
  refine ⟨π, isHallSubgroup_of (G := G) (π := π) (H := D) ?_ ?_⟩
  · intro q hq_dvd
    exact hq_dvd
  · intro q hq_mem hq_dvd_idx
    exact (Nat.not_coprime_of_dvd_of_dvd q.2.one_lt hq_mem hq_dvd_idx) hcop_index
