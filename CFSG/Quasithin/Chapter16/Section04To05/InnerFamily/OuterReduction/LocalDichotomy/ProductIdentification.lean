module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CommutingConjugates
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Consequences

public import Theory.GroupTheory.NilpotentCommutingConjugate

/-!
# Identifying the commuting-conjugate product in the empty-family argument

Normalizer growth supplies the non-Sylow-centralizing conjugate in the
paragraph after (+). The component center lies in T_C by the proved
center/two-core equality and Sylow containment for normal two-subgroups.

The checked odd-intersection assertion (*) forces any conjugate of K
containing an involution in KL to equal K. Consequently, a D₈ conjugation
identity puts r rˡ in K ∩ L. The exact earlier equality C_TC(R) = ⟨z⟩
then identifies the product with z. Uniform such identities give the full
upper bound on the conjugacy-centralizer intersection.

The A₆ calculation and construction of the invariant subgroup of order four
remain separate obligations. We retain C_TC(R) = ⟨z⟩ explicitly: it is
16.4.4(1), rather than any part of the sought dichotomy.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1190, between (+) and (!).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r l : G} {L R : Subgroup G}

/-- The cover center is a normal two-subgroup of N_G(L), hence lies in T_C.
The two-core equality is the proved source 16.1.2(1). -/
theorem component_center_le_commutingSylow
    (heven : HasEvenTypeCentralizers G) (h : StandardSetup T z L) :
    L ⊓ centralizer (L : Set G) ≤ commutingSylow T L := by
  have hc := heven.component_center_eq_twoCore h.involution h.component
  have hm : (center L).map L.subtype = L ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, fun l hl => congrArg Subtype.val (mem_center_iff.mp hx ⟨l, hl⟩)⟩
    · rintro ⟨hxL, hxC⟩
      refine ⟨⟨x, hxL⟩, mem_center_iff.mpr ?_, rfl⟩
      intro l
      exact Subtype.ext (hxC l l.property)
  have hp : IsPGroup 2 ↥(L ⊓ centralizer (L : Set G)) := by
    rw [← hm, hc]
    exact pCore_isPGroup.map L.subtype
  let H := normalizer (L : Set G)
  let Z := L ⊓ centralizer (L : Set G)
  have hZH : Z ≤ H := inf_le_left.trans L.le_normalizer
  let : (Z.subgroupOf H).Normal := by
    change ((L.subgroupOf H) ⊓ ((centralizer (L : Set G)).subgroupOf H)).Normal
    infer_instance
  have hz := (hp.of_equiv (subgroupOfEquivOfLe hZH).symm).le_sylow_of_normal
    (T.subtype h.sylow_normalizes)
  exact fun x hx => ⟨hz (show (⟨x, hZH hx⟩ : H) ∈ Z.subgroupOf H from hx), hx.2⟩

/-- The non-Sylow-centralizing case immediately after (+). The A₆ exception
of 16.1.6 still requires its separate permutation calculation. -/
theorem exists_commuting_conjugate_of_noncentral_componentSylow
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hnc : r ∉ centralizer (componentSylow T L : Set G)) :
    ∃ l ∈ L, MulAut.conj l r ≠ r ∧ Commute r (MulAut.conj l r) := by
  have hrT := h.le_sylow hr
  have hn : r ∈ normalizer (componentSylow T L : Set G) :=
    inf_normalizer_le_normalizer_inf
      ⟨(T : Subgroup G).le_normalizer hrT, h.sylow_normalizes hrT⟩
  obtain ⟨l, hl, hne, hc⟩ := exists_distinct_commuting_conjugate_in_two_subgroup
    (componentSylow T L) (T.isPGroup'.to_le inf_le_left) hr2 hn hnc
  exact ⟨l, hl.2, hne, hc⟩

/-- The odd-intersection clause (*) forces a conjugate containing an involution
of KL to equal K in the empty-family case. -/
theorem conjugate_eq_of_involution_mem_componentProduct
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) {J : Subgroup G}
    (hJ : ∃ a : G, J = (centralizer (L : Set G)).conjBy a)
    {v : G} (hvJ : v ∈ J) (hv2 : orderOf v = 2)
    (hvKL : v ∈ centralizer (L : Set G) ⊔ L) :
    J = centralizer (L : Set G) := by
  by_contra hne
  have hvN : v ∈ normalizer (centralizer (L : Set G) : Set G) := by
    rw [h.normalizers_eq]
    exact (sup_le (centralizer_le_normalizer _) L.le_normalizer) hvKL
  have hJdelta : J ∈ delta L := by
    refine ⟨hJ, hne, even_iff_two_dvd.mpr ?_⟩
    have ho : orderOf (⟨v, hvJ, hvN⟩ :
        ↥(J ⊓ normalizer (centralizer (L : Set G) : Set G))) = 2 :=
      (orderOf_coe _).symm.trans hv2
    exact ho ▸ orderOf_dvd_natCard _
  have hodd := odd_componentProduct_intersection_of_not_mem_deltaZero h.tight
    h.normalizers_eq hsmall hJdelta (fun hh => hempty ⟨J, hh⟩)
  have ho : orderOf (⟨v, hvJ, hvKL⟩ :
      ↥(J ⊓ (centralizer (L : Set G) ⊔ L))) = 2 :=
    (orderOf_coe _).symm.trans hv2
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (ho ▸ orderOf_dvd_natCard _))

/-- The product of r with its L-conjugate lies in L because r normalizes L. -/
theorem conjugate_product_mem (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L) :
    r * MulAut.conj l r ∈ L := by
  have hrN : r ∈ normalizer (L : Set G) := h.sylow_normalizes (h.le_sylow hr)
  have hri : r⁻¹ = r := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two, hr2] using pow_orderOf_eq_one r
  have hc : r * l * r⁻¹ ∈ L := (mem_normalizer_iff.mp hrN l).mp hl
  simpa only [MulAut.conj_apply, mul_assoc, hri] using L.mul_mem hc (L.inv_mem hl)

omit [Finite G] in
private theorem product_order_two {r s : G} (hr2 : orderOf r = 2)
    (hs2 : orderOf s = 2) (hcomm : Commute r s) (hne : s ≠ r) :
    orderOf (r * s) = 2 := by
  have hrpow : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  have hspow : s ^ 2 = 1 := hs2 ▸ pow_orderOf_eq_one s
  apply orderOf_eq_prime
  · rw [hcomm.mul_pow, hrpow, hspow, one_mul]
  · intro he
    apply hne
    have hrr : r * r = 1 := by simpa only [pow_two] using hrpow
    exact mul_left_cancel (he.trans hrr.symm)

private theorem eq_of_mem_zpowers_of_order_two {v z : G}
    (hz2 : orderOf z = 2) (hv : v ∈ zpowers z) (hv2 : orderOf v = 2) : v = z := by
  classical
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
  have hn2 : n < 2 := by simpa only [Finset.mem_range, hz2] using hn
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · have hv1 : v = 1 := by simpa only [pow_zero] using he.symm
    simp [hv1] at hv2
  · simpa only [pow_one] using he.symm

/-- The D₈ conjugation identity puts the product into a conjugate of K; (*),
followed by C_TC(r) = ⟨z⟩, identifies that product with z. -/
theorem conjugate_product_eq_z_of_dihedral_conjugation
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hcenter : L ⊓ centralizer (L : Set G) ≤ commutingSylow T L)
    (hfixed : commutingSylow T L ⊓ centralizer (R : Set G) = zpowers z)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L)
    (hcomm : Commute r (MulAut.conj l r)) (hne : MulAut.conj l r ≠ r)
    {x : G} (hx : MulAut.conj x (MulAut.conj l r) = r * MulAut.conj l r) :
    r * MulAut.conj l r = z := by
  let J := ((centralizer (L : Set G)).conjBy g).conjBy l
  have hvL := conjugate_product_mem h hr hr2 hl
  have hv2 := product_order_two hr2 (((MulAut.conj l).orderOf_eq r).trans hr2) hcomm hne
  have hvJ : r * MulAut.conj l r ∈ J.conjBy x := by
    exact ⟨MulAut.conj l r, ⟨r, (h.sylow.le hr).1, rfl⟩, hx⟩
  have hJK : J.conjBy x = centralizer (L : Set G) :=
    conjugate_eq_of_involution_mem_componentProduct h.toStandardSetup hsmall hempty
      ⟨x * (l * g), by dsimp [J]; rw [conjBy_conjBy, conjBy_conjBy, mul_assoc]⟩ hvJ hv2
      (mem_sup_right hvL)
  have hvTC : r * MulAut.conj l r ∈ commutingSylow T L :=
    hcenter ⟨hvL, hJK ▸ hvJ⟩
  have hcard : Nat.card R = 2 :=
    hsmall _ h.mem_delta (fun hh => hempty ⟨_, hh⟩) R h.sylow
  have hR : zpowers r = R := eq_of_le_of_card_ge (zpowers_le.mpr hr)
    (by rw [Nat.card_zpowers, hr2, hcard])
  have hvC : r * MulAut.conj l r ∈ centralizer (R : Set G) := by
    rw [← hR, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact ((Commute.refl r).mul_right hcomm).eq.symm
  have hvz : r * MulAut.conj l r ∈ zpowers z := by
    rw [← hfixed]
    exact ⟨hvTC, hvC⟩
  exact eq_of_mem_zpowers_of_order_two h.involution hvz hv2

/-- Uniform D₈ witnesses give the complete conjugacy-centralizer intersection.
The existence and construction of these witnesses is a separate geometric step. -/
theorem commuting_conjugacy_intersection_of_dihedral_conjugation
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hcenter : L ⊓ centralizer (L : Set G) ≤ commutingSylow T L)
    (hfixed : commutingSylow T L ⊓ centralizer (R : Set G) = zpowers z)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hdihedral : ∀ l ∈ L, Commute r (MulAut.conj l r) → MulAut.conj l r ≠ r →
      ∃ x : G, MulAut.conj x (MulAut.conj l r) = r * MulAut.conj l r) :
    ∀ l ∈ L, Commute r (MulAut.conj l r) →
      MulAut.conj l r = r ∨ MulAut.conj l r = r * z := by
  intro l hl hc
  by_cases he : MulAut.conj l r = r
  · exact Or.inl he
  · obtain ⟨x, hx⟩ := hdihedral l hl hc he
    have hv := conjugate_product_eq_z_of_dihedral_conjugation
      h hsmall hempty hcenter hfixed hr hr2 hl hc he hx
    right
    have hrr : r * r = 1 := by simpa only [pow_two, hr2] using pow_orderOf_eq_one r
    rw [← hv, ← mul_assoc, hrr, one_mul]

/-- With one distinct commuting conjugate and the uniform D₈ construction,
the source conjugacy-centralizer intersection is exactly {r, rz}. -/
theorem commuting_conjugacy_intersection_eq
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hcenter : L ⊓ centralizer (L : Set G) ≤ commutingSylow T L)
    (hfixed : commutingSylow T L ⊓ centralizer (R : Set G) = zpowers z)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hexists : ∃ l ∈ L, MulAut.conj l r ≠ r ∧ Commute r (MulAut.conj l r))
    (hdihedral : ∀ l ∈ L, Commute r (MulAut.conj l r) → MulAut.conj l r ≠ r →
      ∃ x : G, MulAut.conj x (MulAut.conj l r) = r * MulAut.conj l r) :
    {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z} := by
  have hbound := commuting_conjugacy_intersection_of_dihedral_conjugation
    h hsmall hempty hcenter hfixed hr hr2 hdihedral
  obtain ⟨l, hl, hne, hc⟩ := hexists
  have he : MulAut.conj l r = r * z := (hbound l hl hc).resolve_left hne
  ext s
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hca⟩
    exact hbound a ha hca
  · intro hs
    rcases hs with hs | hs
    · have hs' : s = r := hs
      subst s
      exact ⟨⟨1, L.one_mem, by simp⟩, Commute.refl r⟩
    · have hs' : s = r * z := hs
      exact hs'.symm ▸ ⟨⟨l, hl, he⟩, he ▸ hc⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
