/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection14.corollary_14_9

open scoped Pointwise

/-! # Corollary 14 10 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem section14_sigmaLength_conjBy
    (x a : G) :
    section14SigmaLength (a⁻¹ * x * a) = section14SigmaLength x := by
  have hPrimeSupport :
      section14ElementPrimeSupport (a⁻¹ * x * a) = section14ElementPrimeSupport x := by
    rw [section14ElementPrimeSupport, section14_zpowers_conjBy_inv]
    exact section14_subgroupPrimeSet_conjBy (G := G) (Subgroup.zpowers x) a⁻¹
  have hSigmaSupport :
      section14SigmaSupport (a⁻¹ * x * a) = section14SigmaSupport x := by
    ext π
    simp [section14SigmaSupport, hPrimeSupport]
  simpa [section14SigmaLength, hSigmaSupport]

private theorem section14_sigmaLength_le_two_of_primeSupport_subset_sigma_union
    {g : G} {M N : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hN : N ∈ section9MaximalSubgroups G)
    (hgπ :
      section14ElementPrimeSupport g ⊆
        section10SigmaPrimes M ∪ section10SigmaPrimes N) :
    section14SigmaLength g ≤ 2 := by
  have hSigmaLe :
      section14SigmaSupport g ⊆
        ({section10SigmaPrimes M, section10SigmaPrimes N} : Set (Set Nat.Primes)) := by
    intro π hπ
    rcases hπ with ⟨hπBlock, ⟨p, hpG, hpπ⟩⟩
    rcases hπBlock with ⟨H, hH, rfl⟩
    rcases hgπ hpG with hpM | hpN
    · have hEq :
          section10SigmaPrimes M = section10SigmaPrimes H :=
        section14_sigma_eq_of_common_prime (G := G) hM hH hpM hpπ
      simp [hEq]
    · have hEq :
          section10SigmaPrimes N = section10SigmaPrimes H :=
        section14_sigma_eq_of_common_prime (G := G) hN hH hpN hpπ
      simp [hEq]
  have hcard :
      Nat.card (section14SigmaSupport g) ≤
        Nat.card ({section10SigmaPrimes M, section10SigmaPrimes N} : Set (Set Nat.Primes)) :=
    Nat.card_mono (by simp) hSigmaLe
  have hpair :
      Nat.card ({section10SigmaPrimes M, section10SigmaPrimes N} : Set (Set Nat.Primes)) ≤ 2 := by
    by_cases hEq : section10SigmaPrimes M = section10SigmaPrimes N
    · simp [hEq]
    · simp [hEq]
  exact le_trans (by simpa [section14SigmaLength] using hcard) hpair

private theorem section14_sigmaLength_le_two_of_mul_of_mem_msigma
    {x y : G} {M N : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hN : N ∈ section9MaximalSubgroups G)
    (hxMσ : x ∈ section10Msigma M)
    (hyNσ : y ∈ section10Msigma N)
    (hcomm : Commute x y) :
    section14SigmaLength (x * y) ≤ 2 := by
  have hxπ :
      section14ElementPrimeSupport x ⊆ section10SigmaPrimes M :=
    section14_primeSupport_subset_sigma_of_msigmaMember
      (G := G) ⟨hM, by simpa using hxMσ⟩
  have hyπ :
      section14ElementPrimeSupport y ⊆ section10SigmaPrimes N :=
    section14_primeSupport_subset_sigma_of_msigmaMember
      (G := G) ⟨hN, by simpa using hyNσ⟩
  have hxyπ :
      section14ElementPrimeSupport (x * y) ⊆
        section10SigmaPrimes M ∪ section10SigmaPrimes N := by
    intro p hpXY
    have hpOrder : p.val ∣ orderOf (x * y) := by
      simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hpXY
    have hpMul : p.val ∣ orderOf x * orderOf y :=
      hpOrder.trans hcomm.orderOf_mul_dvd_mul_orderOf
    rcases p.property.dvd_or_dvd hpMul with hpX | hpY
    · exact Or.inl <| hxπ <| by
        simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hpX
    · exact Or.inr <| hyπ <| by
        simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hpY
  exact
    section14_sigmaLength_le_two_of_primeSupport_subset_sigma_union
      (G := G) hM hN hxyπ

private theorem section14_sigmaLength_le_two_of_mem_tilde
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {g : G} (hg : g ∈ section14Tilde M) :
    section14SigmaLength g ≤ 2 := by
  rcases hg with ⟨x, hxMσ, hxne, r, hr, rfl⟩
  by_cases hr1 : r = 1
  · have hxlen : section14SigmaLength x = 1 :=
      section14_sigmaLength_one_of_mem_msigma (G := G) hM hxMσ hxne
    rw [hr1, mul_one, hxlen]
    omega
  · have hMx : M ∈ section14MsigmaElement x := ⟨hM, by simpa using hxMσ⟩
    obtain ⟨_hx, hσx, hcardx⟩ :=
      section14_nonsingleton_of_mem_R_ne_one (G := G) hr hr1
    have hRdef :
        section14R x = elementCentralizerIn (section10Msigma (section14N x)) x :=
      (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
    have hrCx : r ∈ elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa [hRdef] using hr
    have hNx : section14N x ∈ section9MaximalSubgroups G :=
      (section14N_mem_of_nonsingleton (G := G) hxne hσx hcardx).1
    have hcomm : Commute x r :=
      (Subgroup.mem_centralizer_singleton_iff.mp hrCx.2).symm
    exact
      section14_sigmaLength_le_two_of_mul_of_mem_msigma
        (G := G) hM hNx hxMσ hrCx.1 hcomm

private theorem section14_sigmaLength_le_two_of_alt2
    {y y' : G} {H : Subgroup G}
    (hy'ne : y' ≠ 1)
    (hy'κ : section14IsPiElement (section14KappaPrimes H) y')
    (hy'cent : y' ∈ elementCentralizerIn H y)
    (hHy : H ∈ section14MsigmaElement y) :
    section14SigmaLength (y * y') ≤ 2 := by
  classical
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
  have hsolvH : IsSolvable H :=
    IsMinCE.proper_subgroups_solvable H (lt_top_iff_ne_top.mpr hHP.1.1)
  obtain ⟨K, hK⟩ :=
    section14_exists_hallSubgroupIn (G := G) hsolvH (section14KappaPrimes H)
  obtain ⟨m, hmKelt⟩ :=
    section14_conjugate_kappa_element_into_hall
      (G := G) (M := H) (K := K) hHP hK hy'cent.1 hy'κ
  let y0 : G := (m : G) * y * (m : G)⁻¹
  let y0' : G := (m : G) * y' * (m : G)⁻¹
  have hyHσ : y ∈ section10Msigma H := hHy.2 (by simp)
  have hy0Hσ0 : y0 ∈ section10Msigma (H.conjBy (m : G)) := by
    simpa [y0] using
      section14_mem_msigma_conjBy
        (G := G) (M := H) (x := y) (a := (m : G)) hyHσ
  have hy0Hσ : y0 ∈ section10Msigma H := by
    simpa [y0,
      section11_conjBy_eq_of_mem_normalizer
        (H := H) (Subgroup.le_normalizer m.property)] using hy0Hσ0
  have hcomm1 : Commute y y' :=
    (Subgroup.mem_centralizer_singleton_iff.mp hy'cent.2).symm
  have hcomm0 : Commute y0 y0' := by
    change y0 * y0' = y0' * y0
    have hmul := congrArg (fun t : G => (m : G) * t * (m : G)⁻¹) hcomm1.eq
    simpa [y0, y0', mul_assoc] using hmul
  let Hstar : Subgroup G := section14Theorem14_7Partner H K
  have hHstarP : Hstar ∈ section14MFamilyP G :=
    (theorem_14_7_data (G := G) (M := H) (K := K) hHP hK).1
  have hPartnerK :
      K = section14KStar Hstar (section14KStar H K) :=
    (theorem_14_7_c (G := G) (M := H) (K := K) hHP hK).1
  have hy0'Hstarσ : y0' ∈ section10Msigma Hstar := by
    rw [hPartnerK] at hmKelt
    exact hmKelt.1
  have hy0Len :
      section14SigmaLength (y0' * y0) ≤ 2 :=
    section14_sigmaLength_le_two_of_mul_of_mem_msigma
      (G := G) hHstarP.1 hHP.1 hy0'Hstarσ hy0Hσ hcomm0.symm
  have hConjEq : y0' * y0 = (m : G) * (y * y') * (m : G)⁻¹ := by
    simpa [y0, y0', hcomm1.eq, mul_assoc]
  have hConjLen :
      section14SigmaLength ((m : G) * (y * y') * (m : G)⁻¹) ≤ 2 := by
    simpa [hConjEq] using hy0Len
  have hLenEq :
      section14SigmaLength ((m : G) * (y * y') * (m : G)⁻¹) =
        section14SigmaLength (y * y') := by
    simpa [mul_assoc] using
      (section14_sigmaLength_conjBy (G := G) (x := y * y') (a := (m : G)⁻¹))
  simpa [hLenEq] using hConjLen

/-- Corollary 14.10: every element has `σ`-length at most two. -/
public theorem corollary_14_10 (g : G) :
    section14SigmaLength g ≤ 2 := by
  by_cases hg1 : g = 1
  · subst hg1
    have hbot : subgroupPrimeSet (Subgroup.zpowers (1 : G)) = ∅ := by
      ext p
      simp [subgroupPrimeSet, p.2.ne_one]
    have hSigmaSupport : section14SigmaSupport (1 : G) = ∅ := by
      ext π
      constructor
      · intro hπ
        rcases hπ with ⟨_hπblock, ⟨p, hp1, _hpπ⟩⟩
        rw [section14ElementPrimeSupport, hbot] at hp1
        exact hp1
      · intro hπ
        simpa using hπ
    simp [section14SigmaLength, hSigmaSupport]
  · rcases (lemma_14_6 (G := G) (g := g) hg1).1 with hAlt1 | hAlt2
    · rcases hAlt1 with ⟨x, x', hEq, hxlen, hx'R⟩
      obtain ⟨M, hM⟩ :=
        section14_msigmaElement_nonempty_of_sigmaLength_one (G := G) hxlen
      have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hxlen
      have hgTilde : g ∈ section14Tilde M := by
        refine ⟨x, hM.2 (by simp), hxne, x', hx'R, hEq⟩
      exact
        section14_sigmaLength_le_two_of_mem_tilde
          (G := G) hM.1 hgTilde
    · rcases hAlt2 with ⟨y, y', H, hEq, _hylen, hy'ne, hy'κ, hy'cent, hHy⟩
      simpa [hEq] using
        section14_sigmaLength_le_two_of_alt2
          (G := G) (H := H) hy'ne hy'κ hy'cent hHy

end Section14
