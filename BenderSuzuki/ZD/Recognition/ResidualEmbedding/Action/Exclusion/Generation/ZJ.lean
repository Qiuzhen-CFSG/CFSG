module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces

/-!
# The odd-core product in Corollary 6.4

For a two-point stabilizer `D` and a `p`-subgroup `R` containing an embedded
Sylow subgroup of its odd core `O`, the product `O R` is odd and `R` is
Sylow in it. If the `p'`-core of `O` is trivial, so is that of `O R`:
a normal `p'`-subgroup has trivial image in the `p`-group quotient by `O`.
Glauberman's ZJ theorem therefore makes `O R` normalize `Omega₁(Z(J(R)))`.

Assuming the source odd-core generation statement, the swapping commutator
containment, and a prime divisor of the odd core, this gives both
non-normalization clauses of Corollary 6.4. No oddness of `D` is assumed.
The source generation and local-action premises remain separate obligations.

Source: GLS, Volume 4, Chapter 2, Corollary 6.4, printed p. 43,
`refs/KGroup/GLS4/Chapter2.tex`. The ZJ and coprime Sylow arguments reuse
`SE.Corollary64`, applied to `O R` rather than `D`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
private theorem normal_factor_index_dvd {N R : Subgroup G} [N.Normal]
    (hgen : N ⊔ R = ⊤) : N.index ∣ Nat.card R := by
  have he : N.index = N.relIndex R := by
    rw [← Subgroup.relIndex_top_right, ← hgen, Subgroup.relIndex_sup_left]
  rw [he]
  exact Subgroup.relIndex_dvd_card N R

private theorem normal_factor_core_bot {N R : Subgroup G} [N.Normal]
    (hgen : N ⊔ R = ⊤) (hRp : IsPGroup p R)
    (hN : pPrimeCore p N = ⊥) : pPrimeCore p G = ⊥ := by
  let K := pPrimeCore p G
  obtain ⟨n, hn⟩ := hRp.exists_card_eq
  have hindex : N.index ∣ p ^ n := hn ▸ normal_factor_index_dvd hgen
  have hcop : Nat.Coprime (Nat.card K) N.index :=
    ((pPrimeCore_coprime_card (p := p) (G := G)).symm.pow_right n).of_dvd_right hindex
  have hKN : K ≤ N := Subgroup.relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (Subgroup.relIndex_dvd_card N K)
      (Subgroup.relIndex_dvd_index_of_normal N K))
  have hsub : K.subgroupOf N = ⊥ := by
    apply (pPrimeCore_eq_bot_iff.mp hN) _ (inferInstance)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv]
    exact pPrimeCore_coprime_card
  have hmap := congrArg (Subgroup.map N.subtype) hsub
  simpa [Subgroup.map_subgroupOf_eq_of_le hKN] using hmap

private theorem normal_factor_sylow {N R : Subgroup G} [N.Normal]
    (hgen : N ⊔ R = ⊤) (hRp : IsPGroup p R)
    (P : Sylow p N) (hPR : (P : Subgroup N).map N.subtype ≤ R) :
    ∃ S : Sylow p G, (S : Subgroup G) = R := by
  have hPC : (P : Subgroup N) ≤ R.subgroupOf N := by
    intro x hx
    exact hPR (Subgroup.mem_map_of_mem N.subtype hx)
  have hCP : R.subgroupOf N = (P : Subgroup N) :=
    P.is_maximal' hRp.comap_subtype hPC
  let A : Subgroup G := (P : Subgroup N).map N.subtype
  have hA : A = R ⊓ N := by
    change (P : Subgroup N).map N.subtype = _
    rw [← hCP, Subgroup.subgroupOf_map_subtype]
  have hAN : A ≤ N := Subgroup.map_subtype_le _
  have hAR : A ≤ R := hPR
  have hARindex : A.relIndex R = N.index := by
    rw [hA, Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_left, hgen,
      Subgroup.relIndex_top_right]
  have hANindex : A.relIndex N = (P : Subgroup N).index := by
    change (A.comap N.subtype).index = _
    rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have he : N.index * R.index = (P : Subgroup N).index * N.index := by
    calc
      N.index * R.index = A.index := hARindex ▸ Subgroup.relIndex_mul_index hAR
      _ = (P : Subgroup N).index * N.index :=
        (Subgroup.relIndex_mul_index hAN).symm.trans (congrArg (· * N.index) hANindex)
  have hindex : R.index = (P : Subgroup N).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N)))
    simpa [mul_comm] using he
  exact ⟨hRp.toSylow (by rw [hindex]; exact P.not_dvd_index), rfl⟩

omit [Finite G] in
private theorem normal_factor_odd {N R : Subgroup G} [N.Normal]
    (hgen : N ⊔ R = ⊤) (hN : Odd (Nat.card N)) (hR : Odd (Nat.card R)) :
    Odd (Nat.card G) := by
  rw [← N.card_mul_index]
  exact hN.mul (hR.of_dvd_nat (normal_factor_index_dvd hgen))


/-- The group used in the ZJ argument is the odd-core product, even when
its ambient two-point stabilizer has even order. -/
public theorem action_oddCore_product {D R : Subgroup G}
    (hpOdd : Odd p) (hRp : IsPGroup p R) (hRD : R ≤ D)
    (htheta : corollary64Theta p D = ⊥)
    (hcontains : ∃ P₀ : Sylow p (twoPrimeCore D),
      (((P₀ : Subgroup (twoPrimeCore D)).map (twoPrimeCore D).subtype).map
        D.subtype) ≤ R) :
    Odd (Nat.card (corollary64OddCore D ⊔ R : Subgroup G)) ∧
    pPrimeCore p (corollary64OddCore D ⊔ R : Subgroup G) = ⊥ ∧
    theorem4bIsSylowSubgroupOf p R (corollary64OddCore D ⊔ R) := by
  let O := corollary64OddCore D
  let H := O ⊔ R
  let N := O.subgroupOf H
  let T := R.subgroupOf H
  have hOH : O ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  have hOD : O ≤ D := Subgroup.map_subtype_le _
  have hDN : D ≤ Subgroup.normalizer (O : Set G) := by
    have : (twoPrimeCore D).Characteristic :=
      pPrimeCore_characteristic (p := 2) (G := D)
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := D) (K := twoPrimeCore D))
  have hHnorm : H ≤ Subgroup.normalizer (O : Set G) :=
    (sup_le hOD hRD).trans hDN
  let : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHnorm
  have hNT : N ⊔ T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOH hRH]
    exact Subgroup.subgroupOf_self _
  have hTp : IsPGroup p T := hRp.comap_subtype
  have hOp : pPrimeCore p O = ⊥ := by
    apply Subgroup.map_injective O.subtype_injective
    simpa [O, corollary64Theta] using htheta
  let eN : N ≃* O := Subgroup.subgroupOfEquivOfLe hOH
  have hNp : pPrimeCore p N = ⊥ := by
    apply Subgroup.map_injective (f := eN.toMonoidHom) eN.injective
    rw [pPrimeCore_map_iso, hOp, Subgroup.map_bot]
  have hOodd : Odd (Nat.card O) := by
    rw [show Nat.card O = Nat.card (twoPrimeCore D) from
      Subgroup.card_map_of_injective D.subtype_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := D))
  have hNodd : Odd (Nat.card N) := (Nat.card_congr eN.toEquiv).symm ▸ hOodd
  have hTodd : Odd (Nat.card T) := by
    obtain ⟨n, hn⟩ := hTp.exists_card_eq
    rw [hn]
    exact hpOdd.pow
  refine ⟨normal_factor_odd hNT hNodd hTodd,
    normal_factor_core_bot hNT hTp hNp, ?_⟩
  obtain ⟨P₀, hPR⟩ := hcontains
  let eO : twoPrimeCore D ≃* O :=
    Subgroup.equivMapOfInjective (twoPrimeCore D) D.subtype D.subtype_injective
  let e := eO.trans eN.symm
  let P : Sylow p N := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPT : (P : Subgroup N).map N.subtype ≤ T := by
    rintro x ⟨y, hy, rfl⟩
    change y ∈ (P₀ : Subgroup (twoPrimeCore D)).map e.toMonoidHom at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact hPR (Subgroup.mem_map_of_mem D.subtype
      (Subgroup.mem_map_of_mem (twoPrimeCore D).subtype ha))
  obtain ⟨S, hS⟩ := normal_factor_sylow hNT hTp P hPT
  refine ⟨S, ?_⟩
  rw [hS]
  exact (Subgroup.map_subgroupOf_eq_of_le hRH).symm


private theorem action_corollary64Z_ne_bot {R : Subgroup G}
    (hRp : IsPGroup p R) (hRne : R ≠ ⊥) :
    corollary64Z ⟨p, Fact.out⟩ R ≠ ⊥ := by
  have hJne : thompsonCenter R ≠ ⊥ :=
    section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hRp hRne
  have hJp : IsPGroup p (thompsonCenter R) := hRp.to_le (thompsonCenter_le R)
  have hpdiv : p ∣ Nat.card (thompsonCenter R) := by
    rcases hJp.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hJne ((Subgroup.card_eq_one).mp hcard))
    · exact hdiv
  simpa [corollary64Z] using omega₁_map_subtype_ne_bot (thompsonCenter R) p hpdiv

/-- Normalizing the ZJ subgroup contradicts odd-core generation. The
commutator hypothesis is Proposition 3.5; only the odd core is assumed
in the generation hypothesis, and no oddness of `D` is needed. -/
public theorem action_corollary64_not_normalizes_of_generation
    {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (ht : IsInvolution t) (hpOdd : Odd p)
    (hgen : residualGenerated M z t = ⊤)
    (htheta : corollary64Theta p (residualPairStabilizer M t) = ⊥)
    (hcomm : ⁅residualPairStabilizer M t, Subgroup.zpowers t⁆ ≤
      corollary64OddCore (residualPairStabilizer M t))
    (hpdiv : p ∣ Nat.card (twoPrimeCore (residualPairStabilizer M t)))
    {R : Subgroup G} (hRp : IsPGroup p R)
    (hRD : R ≤ residualPairStabilizer M t)
    (hcontains : ∃ P₀ : Sylow p (twoPrimeCore (residualPairStabilizer M t)),
      (((P₀ : Subgroup (twoPrimeCore (residualPairStabilizer M t))).map
        (twoPrimeCore (residualPairStabilizer M t)).subtype).map
        (residualPairStabilizer M t).subtype) ≤ R) :
    z ∉ Subgroup.normalizer (corollary64Z ⟨p, Fact.out⟩ R : Set G) ∧
    z ∉ Subgroup.normalizer (R : Set G) := by
  let D := residualPairStabilizer M t
  let O := corollary64OddCore D
  let H := O ⊔ R
  let V := corollary64Z ⟨p, Fact.out⟩ R
  have hOD : O ≤ D := Subgroup.map_subtype_le _
  have hDnormO : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (O : Set G) := by
    have : (twoPrimeCore D).Characteristic :=
      pPrimeCore_characteristic (p := 2) (G := D)
    exact section8_normalizer_map_subtype_le_of_characteristic
      (H := D) (K := twoPrimeCore D)
  have hHnormO : H ≤ Subgroup.normalizer (O : Set G) :=
    (sup_le hOD hRD).trans (Subgroup.le_normalizer.trans hDnormO)
  have hOnorm : (O.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHnormO
  obtain ⟨hHodd, hHp, hRsyl⟩ := action_oddCore_product hpOdd hRp hRD htheta hcontains
  have hHnormV : H ≤ Subgroup.normalizer (V : Set G) :=
    corollary64_zj_normalizer hHp hOnorm hRsyl hHodd
  have htNormO : t ∈ Subgroup.normalizer (O : Set G) :=
    hDnormO (inf_rightConjugate_mem_normalizer_of_isInvolution M ht)
  have htNormH : t ∈ Subgroup.normalizer (H : Set G) := by
    have hOc : O ≤ H.comap (MulAut.conj t).toMonoidHom := by
      intro x hx
      exact (show O ≤ H from le_sup_left)
        ((Subgroup.mem_normalizer_iff.mp htNormO x).mp hx)
    have hRc : R ≤ H.comap (MulAut.conj t).toMonoidHom := by
      intro x hx
      have hc : ⁅t, x⁆ ∈ O := by
        apply hcomm
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t) (hRD hx)
      have he : MulAut.conj t x = ⁅t, x⁆ * x := conj_eq_commutatorElement_mul
      change MulAut.conj t x ∈ H
      rw [he]
      exact H.mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hx)
    exact Subgroup.mem_normalizer_fintype (fun x hx => (sup_le hOc hRc) hx)
  obtain ⟨x, htxR⟩ := corollary64_exists_conjugate_involution_normalizing_sylow
    hHodd ht htNormH (Fact.out : p.Prime) hRsyl
  have htxV : rightConjugateElem t (x : G) ∈ Subgroup.normalizer (V : Set G) :=
    normalizer_le_normalizer_corollary64Z R htxR
  have hRne : R ≠ ⊥ := by
    obtain ⟨P₀, hPR⟩ := hcontains
    intro hRbot
    have hPbot : (((P₀ : Subgroup (twoPrimeCore D)).map
        (twoPrimeCore D).subtype).map D.subtype) = ⊥ :=
      le_bot_iff.mp (hRbot ▸ hPR)
    have hPbot' : (P₀ : Subgroup (twoPrimeCore D)) = ⊥ := by
      apply Subgroup.map_injective (twoPrimeCore D).subtype_injective
      apply Subgroup.map_injective D.subtype_injective
      simpa using hPbot
    exact Sylow.ne_bot_of_dvd_card P₀ hpdiv hPbot'
  have hzNot : z ∉ Subgroup.normalizer (V : Set G) := by
    intro hzV
    let N := Subgroup.normalizer (V : Set G)
    have hxV : (x : G) ∈ N := hHnormV x.property
    have htV : t ∈ N := by
      have hh := N.mul_mem (N.mul_mem hxV htxV) (N.inv_mem hxV)
      simpa [rightConjugateElem, mul_assoc] using hh
    have hON : O ≤ N := (show O ≤ H from le_sup_left).trans hHnormV
    have hcommN : ⁅O, Subgroup.zpowers t⁆ ≤ N := by
      apply Subgroup.commutator_le.mpr
      intro a ha b hb
      have haN := hON ha
      have hbN := Subgroup.zpowers_le.mpr htV hb
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem haN hbN) (N.inv_mem haN)) (N.inv_mem hbN)
    have hLN : residualGenerated M z t ≤ N :=
      sup_le (sup_le (Subgroup.zpowers_le.mpr hzV)
        (Subgroup.zpowers_le.mpr htV)) hcommN
    have hVnormal : V.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_unique (hgen ▸ hLN))
    rcases r.simple.eq_bot_or_eq_top_of_normal V hVnormal with hbot | htop
    · exact action_corollary64Z_ne_bot hRp hRne hbot
    · have hVM : V ≤ M := (Subgroup.map_subtype_le _).trans
        ((thompsonCenter_le R).trans (hRD.trans inf_le_left))
      exact h.proper (top_unique (htop ▸ hVM))
  exact ⟨hzNot, fun hzR => hzNot (normalizer_le_normalizer_corollary64Z R hzR)⟩

end BenderSuzuki.ZD
