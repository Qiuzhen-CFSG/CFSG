module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical.SourceAssembly
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.RankTwo

/-!
# Prime cores in the original centralizer argument

An elementary or extraspecial odd subgroup P whose full normalizer acts
irreducibly on P/Φ(P) controls the odd prime cores of a strongly quasithin
group. Applying A.1.32 to a characteristic supercritical subgroup shows that
P centralizes every other odd prime core. If the p-core is noncyclic, its
supercritical subgroup has rank greater than one, so A.1.32 identifies it
with P and proves P normal. All A.1.21 and A.1.32 inputs are discharged by
their proved source results.

This form uses the whole centralizer normalizer action. It does not require
irreducibility of its Sylow two-subgroup, which need not hold in the S₅ case
of the original 13.1.12 argument. The original centralizer quotient and its
Frattini action are supplied by the source consumer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 13.1.12,
printed pp.873–874; A.1.21 and A.1.32, pp.24–29.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerCore
open Chapter1 Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem omega_class {Y : Type*} [Group Y] {p : ℕ}
    (h : XiOddQuotient p Y) : omega₁ Y (p := p) = ⊤ ∧
      (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥ := by
  have he : Monoid.exponent Y ∣ p := by
    rcases h with ⟨he, _⟩ | ⟨_, _, hx⟩
    · exact he.exponent_dvd_p
    · rw [hx]
  constructor
  · apply top_unique
    intro x _
    apply Subgroup.subset_closure
    change x ^ (p ^ 1) = 1
    simpa only [pow_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he x
  · have hd : _root_.commutator Y ≤ center Y := by
      rcases h with ⟨hE, _⟩ | ⟨hE, _, _⟩
      · let _ := hE
        rw [commutator_eq_bot]
        exact bot_le
      · let _ := hE.quotient_elementary_abelian
        exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ, top_lowerCentralSeries_one]
    exact bot_unique ((commutator_mono hd le_rfl).trans (commutator_center_left ⊤).le)

private theorem cyclic_of_odd_primeRank_le_one {Y : Type*} [Group Y] [Finite Y]
    {r : ℕ} [Fact r.Prime] (hr : Odd r) (hY : IsPGroup r Y)
    (hm : primeRank r Y ≤ 1) : IsCyclic Y := by
  apply hY.isCyclic_of_odd_of_elementary_card_le hr
  intro E he
  let _ := he
  exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hm E

private theorem supercritical_map_data {Y : Type u} [Group Y] [Finite Y]
    {r : ℕ} (N : Subgroup Y) [N.Normal] (hN : IsPGroup r N)
    (D : Subgroup N) (hD : IsSupercriticalPSubgroup r D)
    (hrank : primeRank r Y ≤ 2) :
    let R := D.map N.subtype
    R.Normal ∧ IsPGroup r R ∧ omega₁ R (p := r) = ⊤ ∧
      (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥ ∧ primeRank r R ≤ 2 := by
  let R := D.map N.subtype
  let e : D ≃* R := D.equivMapOfInjective N.subtype N.subtype_injective
  let _ : D.Characteristic := hD.characteristic
  refine ⟨ConjAct.normal_of_characteristic_of_normal, (hN.to_subgroup D).map _,
    ?_, ?_, (primeRank_subgroup_le r R).trans hrank⟩
  · apply top_unique
    intro x _
    apply Subgroup.subset_closure
    change x ^ (r ^ 1) = 1
    simpa only [pow_one, map_pow, map_one, e.apply_symm_apply] using
      congrArg e (hD.pow_eq_one (e.symm x))
  · have hm := congrArg (Subgroup.map e.toMonoidHom) hD.lowerCentralSeries_two
    simpa only [Subgroup.map_lowerCentralSeries,
      map_top_of_surjective e.toMonoidHom e.surjective, Subgroup.map_bot] using hm

private theorem primeRank_le_one_of_cyclic {Y : Type*} [Group Y] [Finite Y]
    {r : ℕ} [Fact r.Prime] (hY : IsCyclic Y) : primeRank r Y ≤ 1 := by
  classical
  let _ := hY
  let S : Sylow r Y := Classical.choice inferInstance
  exact S.primeRank_le_one_of_isCyclic inferInstance

/-- Coprime detection extends pointwise centralization of the actual
supercritical subgroup to its entire prime core. -/
private theorem centralizes_core_of_supercritical
    {Y : Type u} [Group Y] [Finite Y] {r p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hr : Odd r) (hrp : r ≠ p) (N P : Subgroup Y) [N.Normal]
    (hN : IsPGroup r N) (hP : IsPGroup p P)
    (D : Subgroup N) (hD : IsSupercriticalPSubgroup r D)
    (hc : ⁅D.map N.subtype, P⁆ = ⊥) : P ≤ centralizer (N : Set Y) := by
  let _ := conjMulDistribMulActionOfLeNormalizer P N le_normalizer_of_normal
  let ρ : P →* MulAut N := MulDistribMulAction.toMulAut P N
  have hcop : Nat.Coprime p r := (Nat.coprime_primes Fact.out Fact.out).mpr hrp.symm
  have hcent : P ≤ centralizer (D.map N.subtype : Set Y) := by
    exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hc)
  intro a ha
  have hid : ρ (⟨a, ha⟩ : P) = 1 := by
    apply source_supercriticalCoprimeDetection r hr N hN D hD
    · exact (hP.orderOf_coprime hcop (⟨a, ha⟩ : P)).coprime_dvd_left
        (orderOf_map_dvd ρ _)
    · intro d
      apply Subtype.ext
      change a * (d : Y) * a⁻¹ = (d : Y)
      have he := (mem_centralizer_iff.mp (hcent ha)) (d : Y)
        (mem_map_of_mem N.subtype d.property)
      calc
        a * (d : Y) * a⁻¹ = (d : Y) * a * a⁻¹ := by rw [he]
        _ = (d : Y) := mul_inv_cancel_right _ _
  apply mem_centralizer_iff.mpr
  intro n hn
  have he := congrArg (fun b : MulAut N => ((b ⟨n, hn⟩ : N) : Y)) hid
  change a * n * a⁻¹ = n at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A nonnormal irreducible Ξ subgroup forces the actual p-core to be cyclic. -/
theorem normal_or_cyclic_core {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (P : Subgroup G) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    P.Normal ∨ IsCyclic (pCore p G) := by
  by_cases hc : IsCyclic (pCore p G)
  · exact Or.inr hc
  left
  let N := pCore p G
  obtain ⟨D, hD⟩ := source_supercriticalExistence p ho N pCore_isPGroup
  have hnrank : 1 < primeRank p N := by
    by_contra hm
    exact hc (cyclic_of_odd_primeRank_le_one (Y := N) ho pCore_isPGroup
      (Nat.le_of_not_gt hm))
  have hdrank := source_supercriticalRankDetection p ho N pCore_isPGroup D hD hnrank
  let R := D.map N.subtype
  let e : D ≃* R := D.equivMapOfInjective N.subtype N.subtype_injective
  have hRrank : 1 < primeRank p R := by
    rwa [← primeRank_congr p e]
  have hRne : R ≠ ⊥ := by
    intro he
    have hm := primeRank_le_nat_card (G := R) p
    have hcard : Nat.card R = 1 := by rw [he]; exact Subgroup.card_bot
    omega
  obtain ⟨hn, hpR, hoR, hcR, hmR⟩ := supercritical_map_data N pCore_isPGroup D hD
    (hG p Fact.out ho)
  have hmP := RadicalConjugateRigidity.primeRank_eq_two ho hG P hP
  have hmG : primeRank p G = 2 := le_antisymm (hG p Fact.out ho)
    (hmP.ge.trans (primeRank_subgroup_le p P))
  obtain ⟨hoP, hcP⟩ := omega_class hP
  have hact := source_rankTwoActionImplications p p ho ho G R P
    hn hpR hoR hcR hmR hP.isPGroup hoP hcP hmP hirr
  rcases hact.2 rfl hmG hRne with he | he
  · exact he ▸ hn
  · have hcyc : IsCyclic R := isCyclic_of_prime_card he
    exact (not_le_of_gt hRrank (primeRank_le_one_of_cyclic hcyc)).elim

/-- The same actual irreducible subgroup centralizes every other odd prime core. -/
theorem centralizes_other_cores {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (P : Subgroup G) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
      P ≤ centralizer (pCore r G : Set G) := by
  intro r hr hor hrp
  let _ : Fact r.Prime := ⟨hr⟩
  let N := pCore r G
  obtain ⟨D, hD⟩ := source_supercriticalExistence r hor N pCore_isPGroup
  obtain ⟨hn, hpR, hoR, hcR, hmR⟩ := supercritical_map_data N pCore_isPGroup D hD
    (hG r hr hor)
  obtain ⟨hoP, hcP⟩ := omega_class hP
  have hact := source_rankTwoActionImplications r p hor ho G (D.map N.subtype) P
    hn hpR hoR hcR hmR hP.isPGroup hoP hcP
    (RadicalConjugateRigidity.primeRank_eq_two ho hG P hP) hirr
  exact centralizes_core_of_supercritical hor hrp N P
    pCore_isPGroup hP.isPGroup D hD (hact.1 hrp)

/-- The supercritical core alternative used for the original centralizer quotient.
No local Ξ input or universal earlier-result hypothesis remains. -/
theorem normal_or_core_control {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (P : Subgroup G) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    P.Normal ∨ (IsCyclic (pCore p G) ∧
      ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
        P ≤ centralizer (pCore r G : Set G)) := by
  rcases normal_or_cyclic_core ho hG P hP hirr with hn | hc
  · exact Or.inl hn
  · exact Or.inr ⟨hc, centralizes_other_cores ho hG P hP hirr⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerCore
