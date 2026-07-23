/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection14.corollary_14_8

open scoped Pointwise

/-! # Corollary 14 9 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Corollary 14.9(a): if `𝓜_P` is empty, `G#` is the disjoint union of
the conjugacy closures of the `M̃_i`. -/
public theorem section14_msigmaElement_nonempty_of_sigmaLength_one
    {x : G} (hx : section14SigmaLength x = 1) :
    (section14MsigmaElement x).Nonempty := by
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hx
  obtain ⟨y, y', M, hEq, hy, hy'sigma', hcomm, hMy⟩ :=
    section14_exists_msigma_factor_of_ne_one (G := G) hxne
  let B : Set Nat.Primes := section10SigmaPrimes M
  have hyB : section14ElementPrimeSupport y ⊆ B :=
    section14_primeSupport_subset_sigma_of_msigmaMember hMy
  have hy'Bc : section14ElementPrimeSupport y' ⊆ Bᶜ := hy'sigma'
  have hcop : Nat.Coprime (orderOf y) (orderOf y') :=
    section14_coprime_order_of_support_split
      (π := Bᶜ) (by simpa using hyB) hy'Bc
  have support_mono {a b : G} (hab : a ∈ Subgroup.zpowers b) :
      section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b := by
    intro p hp
    exact section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hab) hp
  have sigmaSupport_mono {a b : G}
      (hab : section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b) :
      section14SigmaSupport a ⊆ section14SigmaSupport b := by
    intro π hπ
    rcases hπ with ⟨hπblock, ⟨p, hpA, hpπ⟩⟩
    exact ⟨hπblock, ⟨p, hab hpA, hpπ⟩⟩
  have sigma_unique :
      ∀ {π₁ π₂ : Set Nat.Primes},
        π₁ ∈ section14SigmaSupport x →
        π₂ ∈ section14SigmaSupport x → π₁ = π₂ := by
    obtain ⟨π0, hπ0, huniq⟩ :=
      section14_unique_sigma_block_of_length_one (G := G) hx
    intro π₁ π₂ h₁ h₂
    exact (huniq _ h₁).trans (huniq _ h₂).symm
  have hB_y : B ∈ section14SigmaSupport y := by
    rw [section14_sigmaSupport_eq_singleton_of_length_one (G := G) hy hMy]
    simp [B]
  have hyG0 : y ∈ Subgroup.zpowers (y * y') :=
    section14_mem_zpowers_mul_of_commute_of_coprime_order hcomm hcop
  have hyG : y ∈ Subgroup.zpowers x := by
    simpa [hEq] using hyG0
  have hB_x : B ∈ section14SigmaSupport x :=
    sigmaSupport_mono (support_mono hyG) hB_y
  have hy'1 : y' = 1 := by
    by_contra hy'ne
    have hy'G0 : y' ∈ Subgroup.zpowers (y' * y) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hcomm.symm (by simpa [Nat.coprime_comm] using hcop)
    have hy'G1 : y' ∈ Subgroup.zpowers (y * y') := by
      simpa [hcomm.eq] using hy'G0
    have hy'G : y' ∈ Subgroup.zpowers x := by
      simpa [hEq] using hy'G1
    obtain ⟨M1, hM1, hMeet1⟩ :=
      section14_exists_sigma_support_witness (G := G) hy'ne
    let B1 : Set Nat.Primes := section10SigmaPrimes M1
    have hB1_y' : B1 ∈ section14SigmaSupport y' := by
      exact ⟨⟨M1, hM1, rfl⟩, hMeet1⟩
    have hB1_x : B1 ∈ section14SigmaSupport x :=
      sigmaSupport_mono (support_mono hy'G) hB1_y'
    have hEqB : B1 = B := sigma_unique hB1_x hB_x
    rcases hB1_y' with ⟨_hB1block, ⟨q, hqSupp, hqB1⟩⟩
    exact (hy'Bc hqSupp) (hEqB ▸ hqB1)
  refine ⟨M, ?_⟩
  have hyx : y = x := by
    simpa [hy'1] using hEq.symm
  simpa [hyx] using hMy

public theorem corollary_14_9_a
    {n : ℕ} {Ms : Fin n → Subgroup G}
    (hMs : section14ConjugacyClassRepresentatives Ms)
    (hPempty : section14MFamilyP G = ∅) :
    (∀ i j : Fin n, i ≠ j →
      section14ConjugacyClosure (section14Tilde (Ms i)) ∩
        section14ConjugacyClosure (section14Tilde (Ms j)) = ∅) ∧
      ({g : G | g ≠ 1} : Set G) =
        ⋃ i : Fin n, section14ConjugacyClosure (section14Tilde (Ms i)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hMi : Ms i ∈ section9MaximalSubgroups G := hMs.1 i
    have hMj : Ms j ∈ section9MaximalSubgroups G := hMs.1 j
    have hnotconj : ¬ section14ConjugateSubgroups (Ms i) (Ms j) := by
      intro hconj
      obtain ⟨k, hk, huniq⟩ := hMs.2 (Ms i) hMi
      have hik : i = k := huniq i ⟨1, (section8_conjBy_one (G := G) (Ms i)).symm⟩
      have hjk : j = k := huniq j hconj
      exact hij (hik.trans hjk.symm)
    exact section14_conjClosure_tilde_disjoint_of_not_conjugate
      (G := G) hMj hMi hnotconj
  · apply Set.Subset.antisymm
    · intro g hg
      rcases (lemma_14_6 (G := G) (g := g) hg).1 with hAlt1 | hAlt2
      · rcases hAlt1 with ⟨x, r, rfl, hxlen, hr⟩
        have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hxlen
        have hσx : (section14MsigmaElement x).Nonempty :=
          section14_msigmaElement_nonempty_of_sigmaLength_one (G := G) hxlen
        let Mx : Subgroup G := Classical.choose hσx
        have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
        obtain ⟨i, hiConj, _hiuniq⟩ := hMs.2 Mx hMx.1
        have hxConj : x ∈ section14ConjClosureMsigmaNonid (Ms i) :=
          section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
            (G := G) (M := Ms i) (L := Mx) hiConj (hMx.2 (by simp)) hxne
        have hxr :
            x * r ∈ section14ConjugacyClosure (section14Tilde (Ms i)) :=
          section14_mul_mem_conjClosureTilde_of_mem_conjClosureMsigmaNonid
            (G := G) (M := Ms i) hxConj hr
        exact Set.mem_iUnion.mpr ⟨i, hxr⟩
      · rcases hAlt2 with ⟨y, y', M, _hEq, _hylen, hy'ne, hy'κ, hy'cent, hMy⟩
        obtain ⟨q, z, hz_zpowy', _hzY', _hz_ne, hzprime⟩ :=
          section14_exists_primeOrder_zpowers_in (G := G)
            (B := Subgroup.zpowers y') (Subgroup.mem_zpowers y') hy'ne
        have hqSupp : q ∈ section14ElementPrimeSupport y' := by
          have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
            rw [subgroupPrimeSet]
            rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
              ⟨_hzle, hqcard⟩
            simp [hqcard]
          simpa [section14ElementPrimeSupport] using
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 hz_zpowy') hqz
        have hMP : M ∈ section14MFamilyP G := ⟨hMy.1, ⟨q, hy'κ hqSupp⟩⟩
        simp [hPempty] at hMP
    · intro g hg
      rcases Set.mem_iUnion.mp hg with ⟨i, hgi⟩
      intro hg1
      exact section14_one_not_mem_conjClosure_tilde (G := G) (M := Ms i) (hMs.1 i) (hg1 ▸ hgi)

public theorem section14_conjugate_kappa_element_into_hall
    {M K : Subgroup G} {x : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hxM : x ∈ M)
    (hxκ : section14IsPiElement (section14KappaPrimes M) x) :
    ∃ m : M, (m : G) * x * (m : G)⁻¹ ∈ K := by
  classical
  let Ysub : Subgroup M := (Subgroup.zpowers x).subgroupOf M
  have hYleM : Subgroup.zpowers x ≤ M := Subgroup.zpowers_le.2 hxM
  have hYsubπ : IsPiSubgroup (G := M) (section14KappaPrimes M) Ysub := by
    intro p hpYsub
    have hpY : p ∈ subgroupPrimeSet (Subgroup.zpowers x) := by
      have hcard : Nat.card Ysub = Nat.card (Subgroup.zpowers x) :=
        section12_card_subgroupOf_eq hYleM
      simpa [Ysub, subgroupPrimeSet, hcard] using hpYsub
    simpa [section14ElementPrimeSupport] using hxκ hpY
  letI : MulDistribMulAction Unit M := {
    smul := fun _ z => z
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hYsubInv : IsInvariant Unit M Ysub := by
    refine ⟨?_⟩
    intro _ z
    simp [Ysub]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Lsub, hLHall, _hLInv, hYsubL⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
      Ysub hYsubπ hYsubInv
  obtain ⟨m, hm⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hsolvM hLHall hK.2
  have hYsubConjLe :
      Ysub.map (MulAut.conj m).toMonoidHom ≤ K.subgroupOf M := by
    have htmp :
        Ysub.map (MulAut.conj m).toMonoidHom ≤
          Lsub.map (MulAut.conj m).toMonoidHom :=
      Subgroup.map_mono hYsubL
    simpa [hm] using htmp
  have hYconjLe :
      (Subgroup.zpowers x).conjBy (m : G) ≤ K := by
    simpa [Ysub] using
      section14_conjBy_le_of_subgroupOf_conjBy_le
        (G := G) (H := Subgroup.zpowers x) (K := K) (M := M) (g := (m : G))
        m.property hYleM hYsubConjLe
  exact ⟨m, hYconjLe <| Subgroup.mem_map.mpr ⟨x, Subgroup.mem_zpowers x, by
    simp [MulAut.conj_apply, mul_assoc]⟩⟩

public theorem section14_mem_kstar_of_mem_msigma_of_mem_hall_of_commute
    {M K : Subgroup G} {x y : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hyMσ : y ∈ section10Msigma M)
    (hxK : x ∈ K)
    (hxne : x ≠ 1)
    (hcomm : Commute y x) :
    y ∈ section14KStar M K := by
  classical
  obtain ⟨q, z, hz_zpowx, _hzK, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  obtain ⟨U, h14a⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMσ, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hwX
    have hwx : w ∈ Subgroup.zpowers x := (Subgroup.zpowers_le.2 hz_zpowx) hwX
    rcases Subgroup.mem_zpowers_iff.mp hwx with ⟨n, rfl⟩
    exact (hcomm.zpow_right n).eq.symm
  simpa [section14_b1_centralizer_eq_kstar_of_prime_manner
    (G := G) (M := M) (K := K) (X := X) h14a.1 hX] using hyCentX

public theorem section14_mul_mem_widehatZ_of_mem_hall_of_mem_kstar
    {M K : Subgroup G} {x y : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hxK : x ∈ K)
    (hxne : x ≠ 1)
    (hyKstar : y ∈ section14KStar M K)
    (hyne : y ≠ 1) :
    x * y ∈ section14WidehatZ M K := by
  classical
  obtain ⟨q, z, hz_zpowx, _hzK, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  have hZdp : section14ZInternalDirectProduct M K :=
    (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X hX).2.2
  have hxNotKstar : x ∉ section14KStar M K := by
    intro hxKstar
    have hxBot : x ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hxK hxKstar
    exact hxne (Subgroup.mem_bot.mp hxBot)
  have hyNotK : y ∉ K := by
    intro hyK
    have hyBot : y ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hyK hyKstar
    exact hyne (Subgroup.mem_bot.mp hyBot)
  have hxyZ : x * y ∈ section14Z M K := by
    change x * y ∈ K ⊔ section14KStar M K
    simpa [section14Z] using Subgroup.mul_mem_sup hxK hyKstar
  have hxyNotK : x * y ∉ K := by
    intro hxyK
    have hyK : y ∈ K := by
      have hyEq : y = x⁻¹ * (x * y) := by
        group
      rw [hyEq]
      exact K.mul_mem (K.inv_mem hxK) hxyK
    exact hyNotK hyK
  have hxyNotKstar : x * y ∉ section14KStar M K := by
    intro hxyKstar
    have hxKstar : x ∈ section14KStar M K := by
      have hxEq : x = (x * y) * y⁻¹ := by
        group
      rw [hxEq]
      exact (section14KStar M K).mul_mem hxyKstar ((section14KStar M K).inv_mem hyKstar)
    exact hxNotKstar hxKstar
  exact ⟨hxyZ, by
    intro hxyUnion
    rcases hxyUnion with hxyK | hxyKstar
    · exact hxyNotK hxyK
    · exact hxyNotKstar hxyKstar⟩

/-- Corollary 14.9(b): if `𝓜_P` is nonempty, `G#` is the disjoint union
of `𝓒_G(Ẑ)` and the conjugacy closures of the `M̃_i`. -/
public theorem corollary_14_9_b
    {n : ℕ} {Ms : Fin n → Subgroup G}
    (hMs : section14ConjugacyClassRepresentatives Ms)
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (∀ i j : Fin n, i ≠ j →
      section14ConjugacyClosure (section14Tilde (Ms i)) ∩
        section14ConjugacyClosure (section14Tilde (Ms j)) = ∅) ∧
      (∀ i : Fin n,
        section14ConjugacyClosure (section14WidehatZ M K) ∩
          section14ConjugacyClosure (section14Tilde (Ms i)) = ∅) ∧
      ({g : G | g ≠ 1} : Set G) =
        section14ConjugacyClosure (section14WidehatZ M K) ∪
          ⋃ i : Fin n, section14ConjugacyClosure (section14Tilde (Ms i)) := by
  classical
  obtain ⟨Xi0, Mi, _Ki0, hXi0, hMi0, _hKi0, _hKstarKi0, _hMi_not_conj0, _hZleMi0⟩ :=
    section14_7_exists_initial_overgroup_data
      (G := G) (M := M) (K := K) hM hK
  have hMiFam : Mi ∈ section14_7_overgroupFamily K := ⟨Xi0, hXi0, hMi0⟩
  have hP2 :
      M ∈ section14MFamilyP2 G ∨
        ∃ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K ∧ Mj ∈ section14MFamilyP2 G :=
    section14_7_exists_P2_self_or_overgroupFamily (G := G) (M := M) (K := K) hM hK
  rcases
      section14_7_singleton_collapse_of_P2_witness
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam hP2 with
    ⟨huniqFam, _hKiEqBase, hKistarEqK, _hP2Mi⟩
  have hTSetEq :
      section14_7_TSet (G := G) (M := M) (K := K) hM hK = section14WidehatZ M K := by
    exact
      section14_7_TSet_eq_widehatZ_of_singleton
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK
  let Mstar : Subgroup G := section14Theorem14_7Partner M K
  have hMstarP : Mstar ∈ section14MFamilyP G :=
    (theorem_14_7_data (G := G) (M := M) (K := K) hM hK).1
  have hMstarHall :
      section12HallSubgroupIn (section14KappaPrimes Mstar) (section14KStar M K) Mstar :=
    (theorem_14_7_b (G := G) (M := M) (K := K) hM hK).1
  have hPartnerK :
      K = section14KStar Mstar (section14KStar M K) :=
    (theorem_14_7_c (G := G) (M := M) (K := K) hM hK).1
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hMi' : Ms i ∈ section9MaximalSubgroups G := hMs.1 i
    have hMj' : Ms j ∈ section9MaximalSubgroups G := hMs.1 j
    have hnotconj : ¬ section14ConjugateSubgroups (Ms i) (Ms j) := by
      intro hconj
      obtain ⟨k, hk, huniq⟩ := hMs.2 (Ms i) hMi'
      have hik : i = k := huniq i ⟨1, (section8_conjBy_one (G := G) (Ms i)).symm⟩
      have hjk : j = k := huniq j hconj
      exact hij (hik.trans hjk.symm)
    exact section14_conjClosure_tilde_disjoint_of_not_conjugate
      (G := G) hMj' hMi' hnotconj
  · intro i
    simpa [hTSetEq] using
      section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
        (G := G) (M := M) (K := K) (H := Ms i) hM hK (hMs.1 i)
  · apply Set.Subset.antisymm
    · intro g hg
      rcases (lemma_14_6 (G := G) (g := g) hg).1 with hAlt1 | hAlt2
      · rcases hAlt1 with ⟨x, r, rfl, hxlen, hr⟩
        have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hxlen
        have hσx : (section14MsigmaElement x).Nonempty :=
          section14_msigmaElement_nonempty_of_sigmaLength_one (G := G) hxlen
        let Mx : Subgroup G := Classical.choose hσx
        have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
        obtain ⟨i, hiConj, _hiuniq⟩ := hMs.2 Mx hMx.1
        have hxConj : x ∈ section14ConjClosureMsigmaNonid (Ms i) :=
          section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
            (G := G) (M := Ms i) (L := Mx) hiConj (hMx.2 (by simp)) hxne
        have hxr :
            x * r ∈ section14ConjugacyClosure (section14Tilde (Ms i)) :=
          section14_mul_mem_conjClosureTilde_of_mem_conjClosureMsigmaNonid
            (G := G) (M := Ms i) hxConj hr
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hxr⟩)
      · rcases hAlt2 with ⟨y, y', H, hEq, hylen, hy'ne, hy'κ, hy'cent, hHy⟩
        have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hylen
        obtain ⟨q, z, hz_zpowy', _hzY', _hz_ne, hzprime⟩ :=
          section14_exists_primeOrder_zpowers_in (G := G)
            (B := Subgroup.zpowers y') (Subgroup.mem_zpowers y') hy'ne
        have hqSupp : q ∈ section14ElementPrimeSupport y' := by
          have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
            rw [subgroupPrimeSet]
            rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
              ⟨_hzle, hqcard⟩
            simp [hqcard]
          simpa [section14ElementPrimeSupport] using
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 hz_zpowy') hqz
        have hHP : H ∈ section14MFamilyP G := ⟨hHy.1, ⟨q, hy'κ hqSupp⟩⟩
        rcases theorem_14_7_g (G := G) (M := M) (K := K) hM hK H hHP with hHM | hHPartner
        · rcases hHM with ⟨a, hHa⟩
          have hyHσ : y ∈ section10Msigma H := hHy.2 (by simp)
          rw [hHa] at hyHσ
          have hy1Mσ : a⁻¹ * y * a ∈ section10Msigma M := by
            simpa [section11_conjBy_inv, mul_assoc] using
              section14_mem_msigma_conjBy
                (G := G) (M := M.conjBy a) (x := y) (a := a⁻¹) hyHσ
          have hy'H : y' ∈ H := hy'cent.1
          rw [hHa] at hy'H
          have hy1M : a⁻¹ * y' * a ∈ M := by
            rcases Subgroup.mem_map.mp hy'H with ⟨u, huM, huEq⟩
            have huEq' : a * u * a⁻¹ = y' := by
              simpa [MulAut.conj_apply] using huEq
            have hyEq : a⁻¹ * y' * a = u := by
              calc
                a⁻¹ * y' * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [huEq'.symm]
                _ = u := by simp [mul_assoc]
            simpa [hyEq] using huM
          have hy1κH :
              section14IsPiElement (section14KappaPrimes H) (a⁻¹ * y' * a) :=
            section14_isPiElement_conjBy_inv
              (G := G) (π := section14KappaPrimes H) (x := y') (g := a) hy'κ
          have hy1κMa :
              section14IsPiElement (section14KappaPrimes (M.conjBy a)) (a⁻¹ * y' * a) := by
            simpa [hHa] using hy1κH
          have hy1κM :
              section14IsPiElement (section14KappaPrimes M) (a⁻¹ * y' * a) := by
            simpa [section14_kappaPrimes_conjBy (G := G) M a] using hy1κMa
          obtain ⟨m, hmKelt⟩ :=
            section14_conjugate_kappa_element_into_hall
              (G := G) (M := M) (K := K) hM hK hy1M hy1κM
          let y0 : G := (m : G) * (a⁻¹ * y * a) * (m : G)⁻¹
          let y0' : G := (m : G) * (a⁻¹ * y' * a) * (m : G)⁻¹
          have hy0Mσ0 :
              y0 ∈ section10Msigma (M.conjBy (m : G)) := by
            simpa [y0] using
              section14_mem_msigma_conjBy
                (G := G) (M := M) (x := a⁻¹ * y * a) (a := (m : G)) hy1Mσ
          have hy0Mσ : y0 ∈ section10Msigma M := by
            simpa [y0,
              section11_conjBy_eq_of_mem_normalizer
                (H := M) (Subgroup.le_normalizer m.property)] using hy0Mσ0
          have hy1centMap :
              a⁻¹ * y' * a ∈ (elementCentralizerIn H y).conjBy a⁻¹ := by
            exact Subgroup.mem_map.mpr ⟨y', hy'cent, by simp [MulAut.conj_apply, mul_assoc]⟩
          have hy1cent0 :
              a⁻¹ * y' * a ∈
                elementCentralizerIn (H.conjBy a⁻¹) (a⁻¹ * y * a) := by
            simpa [section14_elementCentralizerIn_conjBy (G := G) H y a⁻¹, mul_assoc] using
              hy1centMap
          have hy1cent :
              a⁻¹ * y' * a ∈ elementCentralizerIn M (a⁻¹ * y * a) := by
            simpa [hHa, section11_conjBy_inv] using hy1cent0
          have hcomm1 : Commute (a⁻¹ * y * a) (a⁻¹ * y' * a) :=
            (Subgroup.mem_centralizer_singleton_iff.mp hy1cent.2).symm
          have hcomm0 : Commute y0 y0' := by
            change y0 * y0' = y0' * y0
            have hmul := congrArg (fun t : G => (m : G) * t * (m : G)⁻¹) hcomm1.eq
            simpa [y0, y0', mul_assoc] using hmul
          have hy0ne : y0 ≠ 1 := by
            intro hy01
            have hconj := congrArg (fun t : G => (m : G)⁻¹ * t * (m : G)) hy01
            have hy1ne : a⁻¹ * y * a ≠ 1 := by
              intro hy11
              have hback := congrArg (fun t : G => a * t * a⁻¹) hy11
              exact hyne (by simpa [mul_assoc] using hback)
            exact hy1ne (by simpa [y0, mul_assoc] using hconj)
          have hy0'ne : y0' ≠ 1 := by
            intro hy01
            have hconj := congrArg (fun t : G => (m : G)⁻¹ * t * (m : G)) hy01
            have hy1'ne : a⁻¹ * y' * a ≠ 1 := by
              intro hy11
              have hback := congrArg (fun t : G => a * t * a⁻¹) hy11
              exact hy'ne (by simpa [mul_assoc] using hback)
            exact hy1'ne (by simpa [y0', mul_assoc] using hconj)
          have hy0Kstar : y0 ∈ section14KStar M K :=
            section14_mem_kstar_of_mem_msigma_of_mem_hall_of_commute
              (G := G) (M := M) (K := K) hM hK hy0Mσ hmKelt hy0'ne hcomm0
          have hxyWidehat : y0' * y0 ∈ section14WidehatZ M K :=
            section14_mul_mem_widehatZ_of_mem_hall_of_mem_kstar
              (G := G) (M := M) (K := K) hM hK hmKelt hy0'ne hy0Kstar hy0ne
          have htWidehat : y0 * y0' ∈ section14WidehatZ M K := by
            simpa [hcomm0.eq] using hxyWidehat
          exact Or.inl <| by
            refine ⟨y0 * y0', htWidehat, (m : G) * a⁻¹, ?_⟩
            simpa [y0, y0', hEq, mul_assoc]
        · rcases hHPartner with ⟨a, hHa⟩
          have hyHσ : y ∈ section10Msigma H := hHy.2 (by simp)
          rw [hHa] at hyHσ
          have hy1Mstarσ : a⁻¹ * y * a ∈ section10Msigma Mstar := by
            simpa [section11_conjBy_inv, mul_assoc, Mstar] using
              section14_mem_msigma_conjBy
                (G := G) (M := Mstar.conjBy a) (x := y) (a := a⁻¹) hyHσ
          have hy'H : y' ∈ H := hy'cent.1
          rw [hHa] at hy'H
          have hy1Mstar : a⁻¹ * y' * a ∈ Mstar := by
            rcases Subgroup.mem_map.mp hy'H with ⟨u, huMstar, huEq⟩
            have huEq' : a * u * a⁻¹ = y' := by
              simpa [MulAut.conj_apply] using huEq
            have hyEq : a⁻¹ * y' * a = u := by
              calc
                a⁻¹ * y' * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [huEq'.symm]
                _ = u := by simp [mul_assoc]
            simpa [hyEq] using huMstar
          have hy1κH :
              section14IsPiElement (section14KappaPrimes H) (a⁻¹ * y' * a) :=
            section14_isPiElement_conjBy_inv
              (G := G) (π := section14KappaPrimes H) (x := y') (g := a) hy'κ
          have hy1κMstarA :
              section14IsPiElement (section14KappaPrimes (Mstar.conjBy a)) (a⁻¹ * y' * a) := by
            simpa [hHa] using hy1κH
          have hy1κMstar :
              section14IsPiElement (section14KappaPrimes Mstar) (a⁻¹ * y' * a) := by
            simpa [section14_kappaPrimes_conjBy (G := G) Mstar a] using hy1κMstarA
          obtain ⟨m, hmKstarElt⟩ :=
            section14_conjugate_kappa_element_into_hall
              (G := G) (M := Mstar) (K := section14KStar M K)
              hMstarP hMstarHall hy1Mstar hy1κMstar
          let y0 : G := (m : G) * (a⁻¹ * y * a) * (m : G)⁻¹
          let y0' : G := (m : G) * (a⁻¹ * y' * a) * (m : G)⁻¹
          have hy0Mstarσ0 :
              y0 ∈ section10Msigma (Mstar.conjBy (m : G)) := by
            simpa [y0] using
              section14_mem_msigma_conjBy
                (G := G) (M := Mstar) (x := a⁻¹ * y * a) (a := (m : G)) hy1Mstarσ
          have hy0Mstarσ : y0 ∈ section10Msigma Mstar := by
            simpa [y0,
              section11_conjBy_eq_of_mem_normalizer
                (H := Mstar) (Subgroup.le_normalizer m.property)] using hy0Mstarσ0
          have hy1centMap :
              a⁻¹ * y' * a ∈ (elementCentralizerIn H y).conjBy a⁻¹ := by
            exact Subgroup.mem_map.mpr ⟨y', hy'cent, by simp [MulAut.conj_apply, mul_assoc]⟩
          have hy1cent0 :
              a⁻¹ * y' * a ∈
                elementCentralizerIn (H.conjBy a⁻¹) (a⁻¹ * y * a) := by
            simpa [section14_elementCentralizerIn_conjBy (G := G) H y a⁻¹, mul_assoc] using
              hy1centMap
          have hy1cent :
              a⁻¹ * y' * a ∈ elementCentralizerIn Mstar (a⁻¹ * y * a) := by
            simpa [hHa, section11_conjBy_inv] using hy1cent0
          have hcomm1 : Commute (a⁻¹ * y * a) (a⁻¹ * y' * a) :=
            (Subgroup.mem_centralizer_singleton_iff.mp hy1cent.2).symm
          have hcomm0 : Commute y0 y0' := by
            change y0 * y0' = y0' * y0
            have hmul := congrArg (fun t : G => (m : G) * t * (m : G)⁻¹) hcomm1.eq
            simpa [y0, y0', mul_assoc] using hmul
          have hy0ne : y0 ≠ 1 := by
            intro hy01
            have hconj := congrArg (fun t : G => (m : G)⁻¹ * t * (m : G)) hy01
            have hy1ne : a⁻¹ * y * a ≠ 1 := by
              intro hy11
              have hback := congrArg (fun t : G => a * t * a⁻¹) hy11
              exact hyne (by simpa [mul_assoc] using hback)
            exact hy1ne (by simpa [y0, mul_assoc] using hconj)
          have hy0'ne : y0' ≠ 1 := by
            intro hy01
            have hconj := congrArg (fun t : G => (m : G)⁻¹ * t * (m : G)) hy01
            have hy1'ne : a⁻¹ * y' * a ≠ 1 := by
              intro hy11
              have hback := congrArg (fun t : G => a * t * a⁻¹) hy11
              exact hy'ne (by simpa [mul_assoc] using hback)
            exact hy1'ne (by simpa [y0', mul_assoc] using hconj)
          have hy0PartnerK :
              y0 ∈ section14KStar Mstar (section14KStar M K) :=
            section14_mem_kstar_of_mem_msigma_of_mem_hall_of_commute
              (G := G) (M := Mstar) (K := section14KStar M K)
              hMstarP hMstarHall hy0Mstarσ hmKstarElt hy0'ne hcomm0
          have hy0K : y0 ∈ K := by
            exact hPartnerK.symm ▸ hy0PartnerK
          have hxyWidehatPartner :
              y0' * y0 ∈ section14WidehatZ Mstar (section14KStar M K) :=
            section14_mul_mem_widehatZ_of_mem_hall_of_mem_kstar
              (G := G) (M := Mstar) (K := section14KStar M K)
              hMstarP hMstarHall hmKstarElt hy0'ne hy0PartnerK hy0ne
          have htWidehat0 : y0 * y0' ∈ section14WidehatZ Mstar (section14KStar M K) := by
            simpa [hcomm0.eq] using hxyWidehatPartner
          have hPartnerZEq :
              section14Z Mstar (section14KStar M K) = section14Z M K := by
            calc
              section14Z Mstar (section14KStar M K) =
                  section14KStar Mstar (section14KStar M K) ⊔ section14KStar M K := by
                    rw [section14Z, sup_comm]
              _ = K ⊔ section14KStar M K := by rw [← hPartnerK]
              _ = section14Z M K := by rw [section14Z]
          have hWidehatPartnerEq :
              section14WidehatZ Mstar (section14KStar M K) = section14WidehatZ M K := by
            ext t
            constructor <;> intro ht
            · rcases ht with ⟨htZ, htUnion⟩
              refine ⟨?_, ?_⟩
              · exact hPartnerZEq ▸ htZ
              · intro htBaseUnion
                apply htUnion
                rw [Set.union_comm]
                rw [← hPartnerK]
                exact htBaseUnion
            · rcases ht with ⟨htZ, htUnion⟩
              refine ⟨?_, ?_⟩
              · exact hPartnerZEq.symm ▸ htZ
              · intro htPartnerUnion
                apply htUnion
                rw [Set.union_comm] at htPartnerUnion
                rw [← hPartnerK] at htPartnerUnion
                exact htPartnerUnion
          have htWidehat : y0 * y0' ∈ section14WidehatZ M K := by
            exact hWidehatPartnerEq ▸ htWidehat0
          exact Or.inl <| by
            refine ⟨y0 * y0', htWidehat, (m : G) * a⁻¹, ?_⟩
            simpa [y0, y0', hEq, mul_assoc]
    · intro g hg
      rcases hg with hgWidehat | hgTilde
      · intro hg1
        have hOneNotWidehat : 1 ∉ section14WidehatZ M K := by
          simp [section14WidehatZ]
        exact
          section14_one_not_mem_conjClosure_of_one_not_mem
            (G := G) (T := section14WidehatZ M K) hOneNotWidehat
            (hg1 ▸ hgWidehat)
      · rcases Set.mem_iUnion.mp hgTilde with ⟨i, hgi⟩
        intro hg1
        exact section14_one_not_mem_conjClosure_tilde
          (G := G) (M := Ms i) (hMs.1 i) (hg1 ▸ hgi)

end Section14
