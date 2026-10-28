module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Conjugate-component intersections in the alternating branches

The empty-family hypothesis and the inner-involution detector force any
conjugate of z in L⟨z⟩ into C_G(L). Centerlessness of L then leaves only z.
Transport gives source (**). The index-two coset calculation puts products
of two marked elements in the relevant conjugate of L⟨z⟩; the singleton
intersection excludes that product and its product with the marked center.

The index-two overgroups and the independent marked elements are still
geometric inputs to the product lemmas. Their construction from the actual
permutation models is required in the A₆ and A₈ applications. None of the
hypotheses assumes that a product is outside the ambient conjugacy class.

The final lemma obtains r = zˣ directly from the compatible Sylow transport
of 16.4.2(4) and T_C = ⟨z⟩. It does not use 16.4.10, which follows 16.4.9.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192. Conjugation here is left conjugation.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An actual alternating-group isomorphism makes the component disjoint from its ambient centralizer. -/
theorem disjoint_centralizer_of_alternating_equiv {L : Subgroup G} {n : ℕ}
    (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) :
    Disjoint L (centralizer (L : Set G)) := by
  apply Subgroup.disjoint_def.mpr
  intro a ha hC
  have hcenter : e ⟨a, ha⟩ ∈ center (alternatingGroup (Fin n)) := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hC b b.property)
  rw [alternatingGroup.center_eq_bot (by simpa using hn), mem_bot] at hcenter
  have hh : (⟨a, ha⟩ : L) = 1 := e.injective (hcenter.trans (map_one e).symm)
  exact congrArg Subtype.val hh

/-- Source (**), before changing the base component by conjugation. -/
theorem conjugate_eq_of_mem_component_zpowers {L : Subgroup G} {z y : G}
    (hn : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G))
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hzK : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hconj : IsConj z y) (hy : y ∈ L ⊔ zpowers z) : y = z := by
  classical
  obtain ⟨x, hx⟩ := isConj_iff.mp hconj
  have hx' : MulAut.conj x z = y := hx
  have hy2 : orderOf y = 2 := by rw [← hx', (MulAut.conj x).orderOf_eq, hz2]
  have hyK : y ∈ centralizer (L : Set G) := by
    by_contra hnot
    have hdet := mem_deltaZero_of_inner_involution hn hsmall
      (J := (centralizer (L : Set G)).conjBy x) ⟨x, rfl⟩
      (show y ∈ (centralizer (L : Set G)).conjBy x from ⟨z, hzK, hx'⟩)
      hy2
      ((sup_le le_sup_right ((zpowers_le.mpr hzK).trans le_sup_left)) hy) hnot
    exact hempty ⟨_, hdet⟩
  have hZK : zpowers z ≤ centralizer (L : Set G) := zpowers_le.mpr hzK
  have hZN : zpowers z ≤ normalizer (L : Set G) :=
    hZK.trans (centralizer_le_normalizer _)
  change y ∈ (↑(L ⊔ zpowers z) : Set G) at hy
  rw [coe_mul_of_right_le_normalizer_left _ _ hZN] at hy
  obtain ⟨l, hl, t, ht, hlt⟩ := hy
  have hlK : l ∈ centralizer (L : Set G) := by
    have hh := (centralizer (L : Set G)).mul_mem hyK
      ((centralizer (L : Set G)).inv_mem (hZK ht))
    rwa [← hlt, mul_inv_cancel_right] at hh
  have hl1 : l = 1 := disjoint_def.mp hdis hl hlK
  have hyZ : y ∈ zpowers z := by
    change l * t = y at hlt
    rw [hl1, one_mul] at hlt
    exact hlt ▸ ht
  have hycases : y = 1 ∨ y = z := by
    have hh := mem_zpowers_iff_mem_range_orderOf.mp hyZ
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
    have hk2 : k < 2 := by simpa only [Finset.mem_range, hz2] using hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  exact hycases.resolve_left (fun hh => by simp [hh] at hy2)

/-- Source (**): the class of z meets (L⟨z⟩)ˣ in its marked central involution only. -/
theorem StandardSetup.conjugate_eq_of_mem_conjugate_component_zpowers
    {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G))) (x : G) {y : G}
    (hconj : IsConj z y)
    (hy : y ∈ (L ⊔ zpowers z).conjBy x) : y = MulAut.conj x z := by
  have hzK : z ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  obtain ⟨a, ha, rfl⟩ := hy
  apply congrArg (MulAut.conj x)
  apply conjugate_eq_of_mem_component_zpowers h.normalizers_eq hsmall hempty hdis hzK h.involution ?_ ha
  obtain ⟨b, hb⟩ := isConj_iff.mp hconj
  apply isConj_iff.mpr
  refine ⟨x⁻¹ * b, ?_⟩
  have hh := congrArg (MulAut.conj x⁻¹) hb
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- A nonidentity product in X distinct from its marked involution gives the two source exclusions u and u zˣ. -/
theorem StandardSetup.paired_products_not_conjugate
    {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G))) (x : G) {u : G}
    (hu : u ∈ (L ⊔ zpowers z).conjBy x)
    (hu1 : u ≠ 1) (huc : u ≠ MulAut.conj x z) :
    ¬ IsConj z u ∧ ¬ IsConj z (u * MulAut.conj x z) := by
  have hc : MulAut.conj x z ∈ (L ⊔ zpowers z).conjBy x :=
    ⟨z, mem_sup_right (mem_zpowers z), rfl⟩
  refine ⟨fun hh => huc (h.conjugate_eq_of_mem_conjugate_component_zpowers
    hsmall hempty hdis x hh hu), ?_⟩
  intro hh
  have he := h.conjugate_eq_of_mem_conjugate_component_zpowers
    hsmall hempty hdis x hh (((L ⊔ zpowers z).conjBy x).mul_mem hu hc)
  have he' : u * MulAut.conj x z = 1 * MulAut.conj x z := by simpa using he
  exact hu1 (mul_right_cancel he')

/-- Two conjugates of z other than zˣ in an index-two overgroup multiply into X. -/
theorem StandardSetup.pair_mem_conjugate_component_zpowers
    {T : Sylow 2 G} {z : G} {L Y : Subgroup G}
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G))) (x : G)
    (hindex : ((L ⊔ zpowers z).conjBy x).relIndex Y = 2)
    {a b : G} (haY : a ∈ Y) (hbY : b ∈ Y)
    (ha : IsConj z a) (hb : IsConj z b)
    (hac : a ≠ MulAut.conj x z) (hbc : b ≠ MulAut.conj x z) :
    a * b ∈ (L ⊔ zpowers z).conjBy x := by
  have haX : a ∉ (L ⊔ zpowers z).conjBy x := fun hh =>
    hac (h.conjugate_eq_of_mem_conjugate_component_zpowers hsmall hempty hdis x ha hh)
  have hbX : b ∉ (L ⊔ zpowers z).conjBy x := fun hh =>
    hbc (h.conjugate_eq_of_mem_conjugate_component_zpowers hsmall hempty hdis x hb hh)
  exact ((((L ⊔ zpowers z).conjBy x).subgroupOf Y).mul_mem_iff_of_index_two hindex
    (a := ⟨a, haY⟩) (b := ⟨b, hbY⟩)).mpr (iff_of_false haX hbX)

/-- The pair and triple exclusions from actual conjugate-component intersections. The product inequality is elementary independence, not a fusion hypothesis. -/
theorem StandardSetup.two_three_products_not_conjugate
    {T : Sylow 2 G} {z : G} {L Y : Subgroup G}
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G))) (x : G)
    (hindex : ((L ⊔ zpowers z).conjBy x).relIndex Y = 2)
    {a b : G} (haY : a ∈ Y) (hbY : b ∈ Y)
    (ha : IsConj z a) (hb : IsConj z b)
    (hac : a ≠ MulAut.conj x z) (hbc : b ≠ MulAut.conj x z)
    (hab : a ≠ b) (habc : a * b ≠ MulAut.conj x z) :
    ¬ IsConj z (a * b) ∧ ¬ IsConj z (a * b * MulAut.conj x z) := by
  have hb2 : b * b = 1 := by
    obtain ⟨k, hk⟩ := isConj_iff.mp hb
    have hk' : MulAut.conj k z = b := hk
    have hz2 : z * z = 1 := by simpa only [pow_two, h.involution] using pow_orderOf_eq_one z
    rw [← hk', ← map_mul, hz2, map_one]
  have hab1 : a * b ≠ 1 := by
    intro he
    apply hab
    calc
      a = a * (b * b) := by rw [hb2, mul_one]
      _ = b := by rw [← mul_assoc, he, one_mul]
  exact h.paired_products_not_conjugate hsmall hempty hdis x
    (h.pair_mem_conjugate_component_zpowers hsmall hempty hdis x hindex haY hbY ha hb hac hbc)
    hab1 habc

/-- The compatible conjugator from 16.4.2(4) sends z to r when T_C = ⟨z⟩. No later assertion that R is Sylow in K′ is needed. -/
theorem IntersectionSetup.involution_eq_conjugate_of_commutingSylow
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (hr : r ∈ R) (hr2 : orderOf r = 2) : r = MulAut.conj g z := by
  classical
  have hrK : r ∈ (centralizer (L : Set G)).conjBy g := (h.sylow.le hr).1
  have hrT : r ∈ (T : Subgroup G).conjBy g :=
    htransport ⟨h.le_sylow hr, ((centralizer (L : Set G)).conjBy g).le_normalizer hrK⟩
  have heq : (commutingSylow T L).conjBy g =
      (T : Subgroup G).conjBy g ⊓ (centralizer (L : Set G)).conjBy g :=
    map_inf _ _ _ (MulAut.conj g).injective
  have hrZ : r ∈ zpowers (MulAut.conj g z) := by
    have hh : r ∈ (commutingSylow T L).conjBy g := heq ▸ ⟨hrT, hrK⟩
    rwa [hTC, Subgroup.conjBy, MonoidHom.map_zpowers] at hh
  have hc2 : orderOf (MulAut.conj g z) = 2 := (MulAut.conj g).orderOf_eq z |>.trans h.involution
  have hh := mem_zpowers_iff_mem_range_orderOf.mp hrZ
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
  have hk2 : k < 2 := by simpa only [Finset.mem_range, hc2] using hk
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · have hr1 : r = 1 := by simpa only [pow_zero] using he.symm
    simp [hr1] at hr2
  · simpa only [pow_one] using he.symm

end CFSG.Quasithin.Chapter16.Intersections
