module
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Reduction

/-!
# Construction and counting for the special branch of I.7.7

Put `N = N_S(R)`, `S₁ = S₀ ∩ N`, and let `B = Rʸ` be the escaping conjugate
constructed in `Structure.Reduction`. The candidate subgroup is `U = N B`.
Its order is `|R|³`. The conjugates `Rᵇ`, for `b ∈ B`, are distinct and have
pairwise trivial intersections. An explicit finite bijection shows that their
nonidentity elements, together with `S₁`, partition `N`.

This partition proves `N_S(N) = U` and `C_N(a) ≤ S₁` for every nonidentity
`a ∈ B`. These are construction lemmas, not a claim that the remaining
specialness and normal-closure assertions have already been established.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7, printed p.428 (PDF p.439).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
namespace TightNormalizerSetup
variable {G : Type*} [Group G] [Finite G]
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
include h

/-- The source's first normalizer has square order. -/
theorem special_normalizer_card
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) :
    Nat.card ↥(S ⊓ normalizer (R : Set G)) = Nat.card R ^ 2 := by
  obtain ⟨_, _, d, _⟩ := h.directProduct
  rw [← Nat.card_congr d.toEquiv, Nat.card_prod, Nat.card_congr e.toEquiv, pow_two]

/-- In the elementary branch the full first normalizer is elementary abelian. -/
theorem special_normalizer_elementary [IsElementaryAbelian 2 R]
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) :
    IsElementaryAbelian 2 ↥(S ⊓ normalizer (R : Set G)) := by
  obtain ⟨_, _, d, _⟩ := h.directProduct
  let f := d.symm.trans (e.prodCongr (MulEquiv.refl R))
  let : IsMulCommutative ↥(S ⊓ normalizer (R : Set G)) := h.normalizer_commutative e
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  apply f.injective
  rw [map_pow, map_one]
  apply Prod.ext
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 R) (f x).1
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 R) (f x).2

/-- The constructed subgroup lies in the normal closure inside `S`. -/
theorem specialJoin_le_normalClosure
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    {y : G} (hy : y ∈ S) :
    (S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y ≤ tightNormalClosure R S :=
  sup_le (h.normalizer_le_normalClosure e hp) (h.conjugate_le_normalClosure hy)

/-- The order computation for `U = N_S(R) Rʸ`, before proving specialness. -/
theorem specialJoin_card
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥) :
    Nat.card ↥((S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y) = Nat.card R ^ 3 := by
  have hd : Disjoint (S ⊓ normalizer (R : Set G)) (conjSubgroup R y) :=
    (disjoint_iff.mpr htriv).symm.mono inf_le_right le_rfl
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hyN.trans inf_le_right) hd,
    h.special_normalizer_card e, card_conjSubgroup]
  ring

omit [Finite G] in
/-- Both factors of `U` normalize `S₁ = S₀ ∩ N_S(R)`. -/
theorem specialJoin_normalizes_intersection {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G)) :
    (S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y ≤
      normalizer (↑((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) : Set G) := by
  have hi : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) =
      (S ⊓ conjSubgroup K g) ⊓ (S ⊓ normalizer (R : Set G)) := by
    rw [← inf_assoc, inf_eq_left.mpr inf_le_left]
  rw [hi]
  apply le_trans _ inf_normalizer_le_normalizer_inf
  refine le_inf ?_ (sup_le (S ⊓ normalizer (R : Set G)).le_normalizer
    (hyN.trans inf_le_right))
  exact (sup_le inf_le_left (hyN.trans inf_le_left)).trans
    ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp h.intersection_normal)

omit h [Finite G] in
/-- The conjugates indexed by `Rʸ` are all distinct. -/
theorem special_conjugates_injective {y : G}
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥) :
    Function.Injective (fun b : conjSubgroup R y => conjSubgroup R (b : G)) := by
  intro a b hab
  change conjSubgroup R (a : G) = conjSubgroup R (b : G) at hab
  have hn : (b : G)⁻¹ * (a : G) ∈ normalizer (R : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change conjSubgroup R ((b : G)⁻¹ * (a : G)) = R
    rw [← conjSubgroup_conjSubgroup, hab, conjSubgroup_inv]
  have hm : (b : G)⁻¹ * (a : G) ∈ conjSubgroup R y ⊓ normalizer (R : Set G) :=
    ⟨(conjSubgroup R y).mul_mem ((conjSubgroup R y).inv_mem b.property) a.property, hn⟩
  rw [htriv] at hm
  exact Subtype.ext (inv_mul_eq_one.mp (mem_bot.mp hm)).symm

omit [Finite G] in
/-- Each indexed conjugate is contained in the first normalizer. -/
theorem special_conjugate_le {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (b : conjSubgroup R y) :
    conjSubgroup R (b : G) ≤ S ⊓ normalizer (R : Set G) := by
  exact (conjSubgroup_mono (le_inf h.hRS R.le_normalizer) b).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hyN b.property).2)

/-- Distinct members of the constructed conjugate family meet trivially. -/
theorem special_conjugates_disjoint {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    {a b : conjSubgroup R y} (hab : a ≠ b) :
    Disjoint (conjSubgroup R (a : G)) (conjSubgroup R (b : G)) := by
  exact h.pgroupSetup.family_disjoint
    (h.pgroupSetup.family_conjugate h.pgroupSetup.mem_family (hyN a.property).1)
    (h.pgroupSetup.family_conjugate h.pgroupSetup.mem_family (hyN b.property).1)
    (fun he => hab (special_conjugates_injective htriv he))

/-- Every `S`-conjugate remains disjoint from `S₀`, since `S₀` is normal in `S`. -/
theorem special_conjugate_disjoint_intersection {s : G} (hs : s ∈ S) :
    Disjoint (S ⊓ conjSubgroup K g) (conjSubgroup R s) := by
  have hn := (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
    h.intersection_normal hs
  rw [← mem_normalizer_iff_map_conj_eq.mp hn]
  exact Subgroup.disjoint_map (MulAut.conj s).injective h.intersection_disjoint

/-- The counting step in I.7.7: outside `S₁`, every element of `N_S(R)`
lies in exactly one of the `Rʸ`-indexed conjugates of `R`. -/
theorem special_conjugates_cover
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    {x : G} (hx : x ∈ S ⊓ normalizer (R : Set G))
    (hx1 : x ∉ (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) :
    ∃! b : conjSubgroup R y, x ∈ conjSubgroup R (b : G) := by
  classical
  let S1 := (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)
  let N := S ⊓ normalizer (R : Set G)
  let B := conjSubgroup R y
  let D := S1 ⊕ B × {r : R // r ≠ 1}
  let f : D → N := Sum.elim
    (fun s => ⟨s, s.property.1.1, s.property.2⟩)
    (fun br => ⟨MulAut.conj (br.1 : G) (br.2.1 : G),
      h.special_conjugate_le hyN br.1 ⟨br.2.1, br.2.1.property, rfl⟩⟩)
  have hnon : ∀ (b : B) (r : {r : R // r ≠ 1}),
      MulAut.conj (b : G) (r.1 : G) ≠ 1 := by
    intro b r he
    apply r.property
    apply Subtype.ext
    apply (MulAut.conj (b : G)).injective
    simpa only [Subgroup.coe_one, map_one] using he
  have hcross : ∀ (s : S1) (b : B) (r : {r : R // r ≠ 1}),
      (s : G) ≠ MulAut.conj (b : G) (r.1 : G) := by
    intro s b r he
    apply hnon b r
    exact (h.special_conjugate_disjoint_intersection (hyN b.property).1).le_bot
      ⟨he ▸ s.property.1, ⟨r.1, r.1.property, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro u v huv
    have hv := congrArg Subtype.val huv
    cases u with
    | inl s =>
      cases v with
      | inl t => exact congrArg Sum.inl (Subtype.ext hv)
      | inr br => exact (hcross s br.1 br.2 hv).elim
    | inr ar =>
      cases v with
      | inl t => exact (hcross t ar.1 ar.2 hv.symm).elim
      | inr br =>
        change MulAut.conj (ar.1 : G) (ar.2.1 : G) =
          MulAut.conj (br.1 : G) (br.2.1 : G) at hv
        have hab : ar.1 = br.1 := by
          by_contra hne
          apply hnon ar.1 ar.2
          exact (h.special_conjugates_disjoint hyN htriv hne).le_bot
            ⟨⟨ar.2.1, ar.2.1.property, rfl⟩,
              hv.symm ▸ (show MulAut.conj (br.1 : G) (br.2.1 : G) ∈
                conjSubgroup R (br.1 : G) from ⟨br.2.1, br.2.1.property, rfl⟩)⟩
        apply congrArg Sum.inr
        apply Prod.ext hab
        apply Subtype.ext
        apply Subtype.ext
        apply (MulAut.conj (ar.1 : G)).injective
        change MulAut.conj (ar.1 : G) (ar.2.1 : G) =
          MulAut.conj (br.1 : G) (br.2.1 : G) at hv
        simpa only [hab] using hv
  have hc : Nat.card D = Nat.card N := by
    let := Fintype.ofFinite R
    have hr : Nat.card {r : R // r ≠ 1} = Nat.card R - 1 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
    change Nat.card (S1 ⊕ B × {r : R // r ≠ 1}) = Nat.card N
    rw [Nat.card_sum, Nat.card_prod, hr, Nat.card_congr e.toEquiv,
      card_conjSubgroup, h.special_normalizer_card e]
    have hp := Nat.card_pos (α := R)
    have he : Nat.card R - 1 + 1 = Nat.card R := Nat.sub_add_cancel hp
    nlinarith
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩).2
  obtain ⟨u, hu⟩ := hsurj ⟨x, hx⟩
  have hv := congrArg Subtype.val hu
  have hex : ∃ b : B, x ∈ conjSubgroup R (b : G) := by
    cases u with
    | inl s =>
      change (s : G) = x at hv
      exact (hx1 (hv ▸ s.property)).elim
    | inr br => exact ⟨br.1, ⟨br.2.1, br.2.1.property, hv⟩⟩
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, hb, ?_⟩
  intro a ha
  by_contra hne
  have hx0 : x = 1 := (h.special_conjugates_disjoint hyN htriv hne).le_bot ⟨ha, hb⟩
  exact hx1 (by simpa only [hx0] using S1.one_mem)

/-- All `S`-conjugates of `R` in the first normalizer occur in the counted family. -/
theorem special_conjugates_exhaust
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    {s : G} (hs : s ∈ S) (hsN : conjSubgroup R s ≤ S ⊓ normalizer (R : Set G)) :
    ∃ b : conjSubgroup R y, conjSubgroup R s = conjSubgroup R (b : G) := by
  obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.hRne
  let x := MulAut.conj s (r : G)
  have hx : x ∈ conjSubgroup R s := ⟨r, r.property, rfl⟩
  have hxne : x ≠ 1 := by
    intro he
    apply hr
    apply Subtype.ext
    apply (MulAut.conj s).injective
    simpa only [Subgroup.coe_one, map_one] using he
  have hx1 : x ∉ (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
    intro hx1
    exact hxne ((h.special_conjugate_disjoint_intersection hs).le_bot ⟨hx1.1, hx⟩)
  obtain ⟨b, hb, _⟩ := h.special_conjugates_cover e hyN htriv (hsN hx) hx1
  refine ⟨b, ?_⟩
  by_contra hne
  exact hxne ((h.pgroupSetup.family_disjoint
    (h.pgroupSetup.family_conjugate h.pgroupSetup.mem_family hs)
    (h.pgroupSetup.family_conjugate h.pgroupSetup.mem_family (hyN b.property).1)
    hne).le_bot ⟨hx, hb⟩)

/-- The transitive conjugate action identifies the second normalizer with the
constructed subgroup `U`. -/
theorem specialJoin_eq_secondNormalizer
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥) :
    (S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y =
      S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G) := by
  apply le_antisymm
  · exact sup_le (le_inf inf_le_left (S ⊓ normalizer (R : Set G)).le_normalizer) hyN
  · intro s hs
    have hsN : conjSubgroup R s ≤ S ⊓ normalizer (R : Set G) :=
      (conjSubgroup_mono (le_inf h.hRS R.le_normalizer) s).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp hs.2)
    obtain ⟨b, hb⟩ := h.special_conjugates_exhaust e hyN htriv hs.1 hsN
    have hn : (b : G)⁻¹ * s ∈ S ⊓ normalizer (R : Set G) := by
      refine ⟨S.mul_mem (S.inv_mem (hyN b.property).1) hs.1, ?_⟩
      apply mem_normalizer_iff_map_conj_eq.mpr
      change conjSubgroup R ((b : G)⁻¹ * s) = R
      rw [← conjSubgroup_conjSubgroup, hb, conjSubgroup_inv]
    have hm := ((S ⊓ normalizer (R : Set G)) ⊔ conjSubgroup R y).mul_mem
      ((le_sup_right : conjSubgroup R y ≤ _ ⊔ conjSubgroup R y) b.property)
      ((le_sup_left : S ⊓ normalizer (R : Set G) ≤ _ ⊔ conjSubgroup R y) hn)
    simpa only [mul_inv_cancel_left] using hm

/-- A nonidentity element of `Rʸ` has no fixed point in `N_S(R) − S₁`.
The following specialness argument upgrades this containment to equality. -/
theorem special_fixed_le_intersection
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (a : conjSubgroup R y) (ha : a ≠ 1) :
    (S ⊓ normalizer (R : Set G)) ⊓ centralizer ({(a : G)} : Set G) ≤
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
  intro x hx
  by_contra hx1
  obtain ⟨b, hb, huniq⟩ := h.special_conjugates_cover e hyN htriv hx.1 hx1
  have hc : x ∈ conjSubgroup R ((a * b : conjSubgroup R y) : G) := by
    change x ∈ conjSubgroup R ((a : G) * (b : G))
    rw [← conjSubgroup_conjSubgroup]
    refine ⟨x, hb, ?_⟩
    change (a : G) * x * (a : G)⁻¹ = x
    rw [hx.2 (a : G) (Set.mem_singleton _), mul_inv_cancel_right]
  exact ha (mul_right_cancel (show a * b = 1 * b by simpa using huniq _ hc))

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
