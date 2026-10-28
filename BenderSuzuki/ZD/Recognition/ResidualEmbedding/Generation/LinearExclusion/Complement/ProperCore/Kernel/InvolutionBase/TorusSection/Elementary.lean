module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Containment
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import Theory.GroupAction.SubgroupConjugation

/-!
# The elementary quotient of the involution closure

Inside M write `A = M°`, `J = C_G(L)`, `K = D ∩ L`, and `R = ⟨Jᴹ⟩`.
The earlier containment puts A and J in R. The actual torus separates A
from J, so `P = A ⊔ J` has order `2q`, whereas R has order `2q²`.

The normalizer condition gives `P < W = N_R(P)`. Each nonidentity torus
element has centralizer J in the two-core. Coprime fixed-point lifting
therefore makes K act freely on `W/P` away from the identity, giving
`|W/P| ≥ q` and hence W = R. This argument uses the permitted order of R
directly and does not identify R with the source's larger normalizer in V.

Now A is central in R with square one. Conjugation by x in R sends the
unique involution u of J to `a*u` for some a in A. Applying conjugation
twice shows that x² centralizes J, so localization puts x² in AJ. If x
lies outside AJ, its centralizer in AJ is exactly A, forcing x² into A.
Elements of AJ already square to one. Thus R/A has exponent two, before
any assertion about the order, normality or abelian structure of [R,K].

Source: GLS, Volume 4, Chapter 2, Lemma 15.6, the paragraph proving
`R₁/M°` elementary abelian in `refs/KGroup/GLS4/Chapter2.tex`, lines
2713–2721. The earlier centralizer-closure collapse remains explicit;
its discharge belongs to the involution-base source assembly.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

private theorem normalizer_full_of_torus_bound
    {H : Type*} [Group H] [Finite H] (R P K : Subgroup H)
    (hRp : IsPGroup 2 R) (hPR : P < R)
    (hKR : K ≤ normalizer (R : Set H)) (hKP : K ≤ normalizer (P : Set H))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hcard : Nat.card R = Nat.card P * (Nat.card K + 1))
    (hfixed : ∀ k ∈ K, k ≠ 1 → R ⊓ centralizer ({k} : Set H) ≤ P) :
    R ≤ normalizer (P : Set H) := by
  let W := R ⊓ normalizer (P : Set H)
  have hPW : P ≤ W := le_inf hPR.le P.le_normalizer
  let : Group.IsNilpotent R := hRp.isNilpotent
  have hproper : P.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact hPR.not_ge
  have hlt := Group.normalizerCondition_of_isNilpotent (P.subgroupOf R) hproper
  obtain ⟨x, hxN, hxP⟩ := SetLike.exists_of_lt hlt
  have hPWne : P.subgroupOf W ≠ ⊤ := by
    intro he
    have hx : (x : H) ∈ W := by
      refine ⟨x.property, ?_⟩
      rw [← subgroupOf_normalizer_eq hPR.le] at hxN
      exact hxN
    exact hxP (subgroupOf_eq_top.mp he hx)
  have hKW : K ≤ normalizer (W : Set H) := by
    apply (le_inf hKR ?_).trans inf_normalizer_le_normalizer_inf
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj k).bijective,
      mem_normalizer_iff_map_conj_eq.mp (hKP hk)]
  let : MulDistribMulAction K W := conjMulDistribMulActionOfLeNormalizer K W hKW
  let : (P.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  have hInv : IsInvariant K W (P.subgroupOf W) := by
    constructor
    intro k w
    exact mem_normalizer_iff.mp (hKP k.property) w
  have hWp : IsPGroup 2 W := hRp.to_le inf_le_left
  let : Group.IsNilpotent W := hWp.isNilpotent
  have hcopW : Nat.Coprime (Nat.card K) (Nat.card W) :=
    hcop.of_dvd_right (card_dvd_of_le (show W ≤ R from inf_le_left))
  have hbound := Theory.GroupAction.card_actor_lt_card_quotient_of_fixed_le
    (B := K) (P.subgroupOf W) hInv inferInstance hcopW hPWne (by
      intro k hk w hw
      apply hfixed k k.property (fun he => hk (Subtype.ext he))
      refine ⟨w.property.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg Subtype.val hw
      change (k : H) * (w : H) * (k : H)⁻¹ = w at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm)
  have hPWcard : Nat.card (P.subgroupOf W) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPW).toEquiv
  have hWcard := (P.subgroupOf W).card_mul_index
  rw [index_eq_card, hPWcard] at hWcard
  have hboundW : Nat.card R ≤ Nat.card W := by
    rw [hcard, ← hWcard]
    exact Nat.mul_le_mul_left _ hbound
  have hWR : W = R := eq_of_le_of_card_ge inf_le_left hboundW
  exact hWR ▸ (show W ≤ normalizer (P : Set H) from inf_le_right)

private theorem squares_of_normalizes_central_involution_extension
    {H : Type*} [Group H] [Finite H] (R A J : Subgroup H) [A.Normal]
    (hJR : J ≤ R) (hJ : Nat.card J = 2) (hdis : Disjoint A J)
    (hAc : A ≤ centralizer (R : Set H)) (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (hRN : R ≤ normalizer (A ⊔ J : Subgroup H))
    (hlocal : R ⊓ centralizer (J : Set H) ≤ A ⊔ J) :
    ∀ x ∈ R, x ^ 2 ∈ A := by
  obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have hu1 : (u : H) ≠ 1 := fun he => hu (Subtype.ext he)
  have huA : (u : H) ∉ A := fun ha => hu1 (disjoint_def.mp hdis ha u.property)
  have hchoices : ∀ j ∈ J, j = 1 ∨ j = u := by
    intro j hj
    by_cases he : j = 1
    · exact Or.inl he
    · exact Or.inr (congrArg Subtype.val (huniq ⟨j, hj⟩ (fun hh => he (congrArg Subtype.val hh))))
  have hcent : ∀ x : H, Commute x (u : H) → x ∈ centralizer (J : Set H) := by
    intro x hx j hj
    rcases hchoices j hj with rfl | rfl
    · simp
    · exact hx.eq.symm
  have hJsq : ∀ j ∈ J, j ^ 2 = 1 := by
    intro j hj
    exact congrArg Subtype.val (hJ ▸ pow_card_eq_one' (x := (⟨j, hj⟩ : J)))
  intro x hx
  by_cases hxP : x ∈ A ⊔ J
  · obtain ⟨a, ha, j, hj, rfl⟩ := mem_sup_of_normal_left.mp hxP
    have hacj : Commute a j := (mem_centralizer_iff.mp (hAc ha) j (hJR hj)).symm
    rw [hacj.mul_pow, hAsq a ha, hJsq j hj, one_mul]
    exact A.one_mem
  have hxu : x * (u : H) * x⁻¹ ∈ A ⊔ J :=
    (mem_normalizer_iff.mp (hRN hx) u).mp ((show J ≤ A ⊔ J from le_sup_right) u.property)
  obtain ⟨a, ha, j, hj, he⟩ := mem_sup_of_normal_left.mp hxu
  have hconj : x * (u : H) * x⁻¹ = a * u := by
    rcases hchoices j hj with rfl | rfl
    · have hc : x * (u : H) * x⁻¹ ∈ A := by simpa only [mul_one] using he ▸ (A.mul_mem ha A.one_mem)
      exact False.elim (huA ((mem_normalizer_iff.mp
        (show x ∈ normalizer (A : Set H) from le_normalizer_of_normal (mem_top x)) u).mpr hc))
    · exact he.symm
  have hax : a * x = x * a := (mem_centralizer_iff.mp (hAc ha) x hx).symm
  have hxu' : x * (u : H) = a * u * x := mul_inv_eq_iff_eq_mul.mp hconj
  have hxxu : Commute (x ^ 2) (u : H) := by
    change x ^ 2 * (u : H) = u * x ^ 2
    calc
      x ^ 2 * (u : H) = x * (x * u) := by simp only [pow_two, mul_assoc]
      _ = x * (a * u * x) := by rw [hxu']
      _ = a * (x * u) * x := by rw [← mul_assoc, ← mul_assoc, ← hax]; group
      _ = a * (a * u * x) * x := by rw [hxu']
      _ = u * x ^ 2 := by
        have haa : a * a = 1 := by simpa only [pow_two] using hAsq a ha
        calc
          a * (a * (u : H) * x) * x = (a * a) * u * (x * x) := by group
          _ = u * x ^ 2 := by rw [haa, one_mul, pow_two]
  have hx2P : x ^ 2 ∈ A ⊔ J := hlocal ⟨R.pow_mem hx 2, hcent _ hxxu⟩
  obtain ⟨b, hb, j, hj, he⟩ := mem_sup_of_normal_left.mp hx2P
  rcases hchoices j hj with rfl | rfl
  · simpa only [mul_one] using he ▸ (A.mul_mem hb A.one_mem)
  · have hbx : b * x = x * b := (mem_centralizer_iff.mp (hAc hb) x hx).symm
    have hxucomm : Commute x (u : H) := by
      change x * (u : H) = u * x
      apply mul_left_cancel (a := b)
      calc
        b * (x * (u : H)) = x * (b * u) := by rw [← mul_assoc, hbx, mul_assoc]
        _ = x * x ^ 2 := by rw [he]
        _ = x ^ 2 * x := (Commute.self_pow x 2).eq
        _ = b * (u * x) := by rw [← he, mul_assoc]
    exact False.elim (hxP (hlocal ⟨hx, hcent x hxucomm⟩))

/-- The involution closure has exponent two modulo the distinguished closure.
The normalizer condition and the actual torus force `R` to normalize `A_M J_M`;
centrality and involution-centralizer localization then put every square in `A_M`.
Only the permitted earlier centralizer-closure collapse remains conditional. -/
public theorem linear_involutionBase_elementary_quotient_of_centralizerClosure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let V := pCore 2 M
  let P := A ⊔ J
  let : A.Normal := distinguishedClosure_normal h.disconnected
  let : R.Normal := normalClosure_normal
  have hAR : A ≤ R :=
    (linear_distinguishedClosure_le_commutatorKernel_of_centralizerClosure
      h r hz hzM ht htM hL hn e hJ hR hAL hcollapse).trans
      linearCommutatorKernel_le_closure
  have hJR : J ≤ R := subset_normalClosure
  have hRV : R ≤ V := linearCentralizerClosure_le_twoCore hR
  have hVp : IsPGroup 2 V := pCore_isPGroup
  have hRp : IsPGroup 2 R := hVp.to_le hRV
  have hJcard : Nat.card J = 2 := linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ
  obtain ⟨hAsq, hAc, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  obtain ⟨hKcard, hfree⟩ := linear_distinguishedClosure_torus_geometry
    h r hz hzM ht htM hL hn e hAL
  have hq : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸
    Nat.pow_le_pow_right (by decide) hn
  have hJC : J ≤ centralizer (K : Set M) := by
    intro j hj k hk
    apply Subtype.ext
    exact mem_centralizer_iff.mp hj k hk.2
  have hKnon : Nontrivial K := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hKcard]
    omega
  let : Nontrivial K := hKnon
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hdis : Disjoint A J := by
    apply disjoint_def.mpr
    intro a ha hj
    have hc : a ∈ A ⊓ centralizer ({(k : M)} : Set M) :=
      ⟨ha, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hJC hj) k k.property).symm⟩
    have hbot : A ⊓ centralizer ({(k : M)} : Set M) = ⊥ :=
      hfree k k.property (fun he => hk (Subtype.ext he))
    simpa only [hbot, mem_bot] using hc
  have hPcard : Nat.card P = 2 * 2 ^ n := by
    rw [show P = A ⊔ J from rfl,
      card_sup_eq_mul_of_normalizes_of_disjoint A J le_normalizer_of_normal hdis,
      hAcard, hJcard, mul_comm]
  have hPR : P < R := by
    apply lt_of_le_not_ge (sup_le hAR hJR)
    intro hRP
    have hc := card_le_of_le hRP
    change Nat.card (linearCentralizerClosure M z t) ≤ Nat.card P at hc
    rw [hR, hPcard] at hc
    nlinarith
  have hlocal := linear_involution_localization_of_centralizerClosure h.disconnected r
    hz hzM ht htM hL hn e hAL hJ hcollapse
  have helement := linear_twoCore_element_centralizer_of_localization
    h.disconnected hz hzM hJ hR hlocal hfree
  have hKP : K ≤ normalizer (P : Set M) :=
    (le_inf (show K ≤ normalizer (A : Set M) from le_normalizer_of_normal)
      ((le_centralizer_iff.mp hJC).trans (centralizer_le_normalizer (J : Set M)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup A J)
  have hodd : Odd (Nat.card K) := by
    rw [show Nat.card K = Nat.card
      (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) from
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv]
    exact pair_inf_proper_residualGenerated_odd h.disconnected r hz hzM ht htM hL
  have hcop : Nat.Coprime (Nat.card K) (Nat.card R) := by
    obtain ⟨m, hm⟩ := hRp.exists_card_eq
    rw [hm]
    exact hodd.coprime_two_right.pow_right m
  have hRN : R ≤ normalizer (P : Set M) :=
    normalizer_full_of_torus_bound R P K hRp hPR le_normalizer_of_normal hKP hcop
      (by change Nat.card (linearCentralizerClosure M z t) = _
          rw [hR, hPcard, hKcard]
          have he : 2 ^ n - 1 + 1 = 2 ^ n := by omega
          rw [he]
          ring)
      (by
        intro k hk hkn x hx
        have hxJ : x ∈ J := (helement k hk hkn).le ⟨hRV hx.1, hx.2⟩
        exact (show J ≤ P from le_sup_right) hxJ)
  exact squares_of_normalizes_central_involution_extension R A J hJR hJcard hdis
    (hAc.trans (centralizer_le hRV)) hAsq hRN
    ((inf_le_inf_right _ hRV).trans hlocal)

end BenderSuzuki.ZD
