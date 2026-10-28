module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Transfers for the exceptional three-dimensional branch

Conjugation identifies the actual normalizer/centralizer quotients and their
prime-to-three residuals. For the inner-action branch, an odd quotient over
the two-core reduces the three-residual containment to the two-core and the
prime-to-p residuals for p > 3. For the outer-action branch, tight embedding
excludes a nontrivial two-subgroup in both centralizers.

These are finite-group deductions used in the proof of Aschbacher–Smith
16.4.8, combined manuscript of 1 March 2004, printed pp.1187–1188. The
linear/unitary model calculations are separate obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.ExceptionalThree

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The conjugate of the centralizer is the centralizer of the actual
conjugate component. -/
theorem centralizer_conjBy (L : Subgroup G) (g : G) :
    (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    rw [mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
    change (MulAut.conj g) w * (MulAut.conj g) y = (MulAut.conj g) y * (MulAut.conj g) w
    simpa only [map_mul] using congrArg (MulAut.conj g) (hy w hw)
  · intro hx
    refine mem_map.mpr ⟨(MulAut.conj g).symm x, ?_, (MulAut.conj g).apply_symm_apply x⟩
    rw [mem_centralizer_iff] at hx ⊢
    intro y hy
    apply (MulAut.conj g).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      hx ((MulAut.conj g) y) (mem_map_of_mem _ hy)

/-- Conjugation restricts to the two normalizers. -/
noncomputable def normalizerConjEquiv (L : Subgroup G) (g : G) :
    normalizer (L : Set G) ≃* normalizer (L.conjBy g : Set G) :=
  ((MulAut.conj g).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq L (MulAut.conj g)))

/-- The normalizer equivalence sends each element to its conjugate. -/
theorem normalizerConjEquiv_apply (L : Subgroup G) (g : G)
    (x : normalizer (L : Set G)) :
    (normalizerConjEquiv L g x : G) = g * x * g⁻¹ := rfl

/-- The quotient isomorphism uses the relative centralizers as its kernels. -/
noncomputable def actionQuotientConjEquiv (L : Subgroup G) (g : G) :
    componentActionQuotient L ≃* componentActionQuotient (L.conjBy g) := by
  let e := normalizerConjEquiv L g
  apply QuotientGroup.congr _ _ e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (MulAut.conj g) (y : G) ∈ centralizer (L.conjBy g : Set G)
    rw [← centralizer_conjBy]
    exact mem_map_of_mem _ hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change ((e.symm x : normalizer (L : Set G)) : G) ∈ centralizer (L : Set G)
    rw [← centralizer_conjBy] at hx
    obtain ⟨y, hy, he⟩ := hx
    have he' : (MulAut.conj g) (((e.symm x : normalizer (L : Set G)) : G)) =
        (x : G) := congrArg Subtype.val (e.apply_symm_apply x)
    exact (show (((e.symm x : normalizer (L : Set G)) : G)) = y from
      (MulAut.conj g).injective (he'.trans he.symm)) ▸ hy

/-- The quotient equivalence is induced by that same conjugation map. -/
theorem actionQuotientConjEquiv_mk (L : Subgroup G) (g : G)
    (x : normalizer (L : Set G)) :
    actionQuotientConjEquiv L g
        (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf
          (normalizer (L : Set G))) x) =
      QuotientGroup.mk' ((centralizer (L.conjBy g : Set G)).subgroupOf
        (normalizer (L.conjBy g : Set G))) (normalizerConjEquiv L g x) := rfl

/-- The actual image of L in N_G(L)/C_G(L). -/
def componentImage (L : Subgroup G) : Subgroup (componentActionQuotient L) :=
  (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))))

/-- The quotient isomorphism preserves the specified component image. -/
theorem map_componentImage_conj (L : Subgroup G) (g : G) :
    (componentImage L).map (actionQuotientConjEquiv L g).toMonoidHom =
      componentImage (L.conjBy g) := by
  let H := normalizer (L : Set G)
  let H' := normalizer (L.conjBy g : Set G)
  let e := normalizerConjEquiv L g
  have he : (L.subgroupOf H).map e.toMonoidHom = (L.conjBy g).subgroupOf H' := by
    apply map_injective H'.subtype_injective
    rw [map_map]
    have heq : H'.subtype.comp e.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp H.subtype := rfl
    rw [heq, ← map_map, map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le (L.conjBy g).le_normalizer]
    rfl
  change ((L.subgroupOf H).map _).map _ = ((L.conjBy g).subgroupOf H').map _
  rw [← he, map_map, map_map]
  rfl

/-- In particular, the exceptional output for H′/K′ is an identification
of the same prime-to-three residual as the output requested for H/K. -/
noncomputable def actionResidualConjEquiv (L : Subgroup G) (g : G) :
    primeToResidual 3 (componentActionQuotient L) ≃*
      primeToResidual 3 (componentActionQuotient (L.conjBy g)) :=
  primeToResidualEquiv 3 (actionQuotientConjEquiv L g)

variable [Finite G] {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual residual normalizes L′, using the transported equality
N_G(K′) = N_G(L′). -/
theorem residual_normalizes_conjugate_component
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2) :
    involutionResidual L r ≤ normalizer (L.conjBy g : Set G) := by
  have hn : normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      normalizer (L.conjBy g : Set G) := by
    change normalizer (((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) : Set G) =
      normalizer ((L.map (MulAut.conj g).toMonoidHom) : Set G)
    rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq, h.normalizers_eq]
  exact (involutionResidual_le_conjugate_normalizer h hr hr2).trans_eq hn

private theorem prime_not_dvd_index_of_residual_le {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) {p : ℕ} (hp : p.Prime) (h : primeToResidual p D ≤ N) :
    ¬ p ∣ N.index := by
  let : Fact p.Prime := ⟨hp⟩
  let S : Sylow p D := Classical.choice inferInstance
  exact fun hd => S.not_dvd_index (hd.trans
    (index_dvd_of_le ((le_primeToResidual_of_isPGroup S.isPGroup').trans h)))

/-- Containment of the two-core and of all relevant odd residuals leaves
only a three-group quotient. Normality is required only inside D. -/
theorem threeResidual_le_of_twoCore_and_odd_residuals
    {D J : Subgroup G} (hn : D ≤ normalizer (J : Set G))
    (hodd : Odd (pCore 2 D).index)
    (htwo : (pCore 2 D).map D.subtype ≤ J)
    (hres : ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card D →
      (primeToResidual p D).map D.subtype ≤ J) :
    (pResidual 3 D).map D.subtype ≤ J := by
  let N := J.subgroupOf D
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have htwoN : pCore 2 D ≤ N := map_le_iff_le_comap.mp htwo
  have hindex : Odd N.index := hodd.of_dvd_nat (index_dvd_of_le htwoN)
  have hq : IsPGroup 3 (D ⧸ N) := by
    rw [isPGroup_iff_primeFactors_card_subset (by decide)]
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpindex : p ∣ N.index := Nat.dvd_of_mem_primeFactors hp
    have hpcard : p ∣ Nat.card D := hpindex.trans N.index_dvd_card
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact hindex.not_two_dvd_nat hpindex
    have hp3 : p = 3 := by
      by_contra hne
      have hlt : 3 < p := by have := hpprime.two_le; omega
      exact prime_not_dvd_index_of_residual_le N hpprime
        (map_le_iff_le_comap.mp (hres p hpprime hlt hpcard)) hpindex
    subst p
    exact Nat.Prime.mem_primeFactors_self (by decide)
  apply map_le_iff_le_comap.mpr
  change pResidual 3 D ≤ N
  exact sInf_le ⟨inferInstance, hq⟩

/-- The inner branch needs only the two-core placement and the intrinsic
prime-rank test after 16.4.5 supplies its ordinary p > 3 identities. -/
theorem threeResidual_le_conjugate_of_twoCore
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hodd : Odd (pCore 2 (involutionResidual L r)).index)
    (htwo : (pCore 2 (involutionResidual L r)).map
      (involutionResidual L r).subtype ≤ L.conjBy g)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card (involutionResidual L r) →
      1 < primeRank p L)
    (hres : ∀ p ∈ residualPrimes (L.conjBy g), 3 < p →
      (primeToResidual p (involutionCentralizer r)).map
        (involutionCentralizer r).subtype = L.conjBy g) :
    (pResidual 3 (involutionResidual L r)).map
      (involutionResidual L r).subtype ≤ L.conjBy g := by
  apply threeResidual_le_of_twoCore_and_odd_residuals
    (residual_normalizes_conjugate_component h hr hr2) hodd htwo
  intro p hp hlt hd
  have hpL : p ∈ residualPrimes L :=
    ⟨hp, hp.odd_of_ne_two (by omega), hrank p hp hlt hd⟩
  have hpL' : p ∈ residualPrimes (L.conjBy g) := by
    rwa [residualPrimes_conjBy]
  exact (embedded_primeToResidual_mono p
    ((involutionResidual_le L r).trans inf_le_right)).trans (hres p hpL' hlt).le

/-- A two-subgroup in both distinct conjugate centralizers is trivial.
This supplies the tight-embedding contradiction in the order-four-center case. -/
theorem two_subgroup_of_both_centralizers_eq_bot
    (h : IntersectionSetup T z L g R) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ centralizer (L : Set G))
    (hQK' : Q ≤ (centralizer (L : Set G)).conjBy g) : Q = ⊥ := by
  have hg : g ∉ normalizer (centralizer (L : Set G) : Set G) := by
    intro hn
    exact h.mem_delta.2.1 (mem_normalizer_iff_map_conj_eq.mp hn)
  have hodd := h.tight.2 g hg
  obtain ⟨n, hc⟩ := IsPGroup.iff_card.mp hQ
  have hcop : (Nat.card Q).Coprime
      (Nat.card ↥(centralizer (L : Set G) ⊓ (centralizer (L : Set G)).conjBy g)) := by
    rw [hc]
    exact hodd.coprime_two_left.pow_left n
  have he := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rwa [inf_eq_left.mpr (le_inf hQK hQK')] at he

/-- The center of L has trivial intersection with K′. In the exceptional
four-center case, a model calculation forcing a nontrivial intersection
therefore gives a contradiction. -/
theorem center_inter_conjugate_centralizer_eq_bot
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) :
    (center L).map L.subtype ⊓ (centralizer (L : Set G)).conjBy g = ⊥ := by
  apply two_subgroup_of_both_centralizers_eq_bot h
  · have hc : IsPGroup 2 (center L) := by
      rw [hG.evenType.component_center_eq_twoCore h.involution h.component]
      exact pCore_isPGroup
    exact (hc.map L.subtype).of_injective (inclusion inf_le_left) (inclusion_injective _)
  · apply inf_le_left.trans
    rintro x ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg L.subtype (mem_center_iff.mp hy ⟨l, hl⟩)
  · exact inf_le_right

omit [Finite G] in
/-- The small-center argument after passage to H′/K′: an element in the
component image inverting an odd subgroup forces that subgroup into the
component image, because the subgroup normalizes it. -/
theorem odd_subgroup_le_of_inverting_element {D J : Subgroup G}
    (hn : D ≤ normalizer (J : Set G)) (hodd : Odd (Nat.card D)) {y : G}
    (hy : y ∈ J) (hinv : ∀ d ∈ D, y * d * y⁻¹ = d⁻¹) : D ≤ J := by
  intro d hd
  have hs : d ^ 2 ∈ J := by
    have hm := J.mul_mem ((mem_normalizer_iff.mp (hn hd) y).mp hy) (J.inv_mem hy)
    have he : d * y * d⁻¹ * y⁻¹ = d ^ 2 := by
      calc
        _ = d * (y * d * y⁻¹)⁻¹ := by group
        _ = d ^ 2 := by rw [hinv d hd, inv_inv, pow_two]
    rwa [he] at hm
  have ho : Odd (orderOf d) := hodd.of_dvd_nat (D.orderOf_dvd_natCard hd)
  obtain ⟨n, he⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one d) ho 1
  rw [pow_one, pow_mul] at he
  rw [he]
  exact J.pow_mem hs n

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.ExceptionalThree
