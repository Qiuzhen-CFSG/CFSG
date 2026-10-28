module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Catalogue.Action

/-!
# Deductions of clauses (5) and (6) in the restricted catalogue

The centralizer upper bound becomes equality because the nontrivial component
Sylow has a nontrivial center. This allows the exact numerical hypotheses of
16.5.7 to be used in clause (5).

For clause (6), the relative Sylow existence theorem places the detected
involution in a Sylow subgroup of J ∩ N_G(K). When Z(L) = 1, the restricted
star projection is injective, and sends a two-central projected involution to
a two-central involution in L*. This contradicts clause (5), applied uniformly
to those relative Sylow subgroups. The detector follows from 16.4.9(1), using
the already proved detector theorem. Thus neither detector nor avoidance is
assumed as the conclusion of the product-obstruction helper.

These are conditional deductions. The uniform clause-(5) premise still has
to be obtained from 16.5.7 in each admissible intersection setup and the model
bounds. The rank-two exclusion is explicit in both restricted conclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.5.6(5), 16.5.7(1), 16.5.10(5)–(6), printed pp.1197–1199.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter16.Intersections
namespace CFSG.Quasithin.Chapter16.Intersections.Catalogue
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- An injective map of the component transports a witnessing Sylow subgroup
and its central involution. The map need not extend to the ambient group. -/
theorem map_twoCentral {L : Subgroup G} {v : L}
    (f : L →* H) (hf : Function.Injective f) (h : IsTwoCentralIn L (v : G)) :
    IsTwoCentralIn f.range (f v) := by
  obtain ⟨hv2, S, ⟨P, rfl⟩, hvS, hcentral⟩ := h
  refine ⟨?_, (P : Subgroup L).map f, ?_, ?_, ?_⟩
  · rw [orderOf_injective f hf, ← orderOf_injective L.subtype L.subtype_injective]
    exact hv2
  · refine ⟨P.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective, ?_⟩
    change ((P : Subgroup L).map f.rangeRestrict).map f.range.subtype = _
    rw [map_map]
    rfl
  · obtain ⟨w, hw, he⟩ := hvS
    exact ⟨w, hw, congrArg f (Subtype.ext he)⟩
  · rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := mem_centralizer_singleton_iff.mp
      (hcentral (mem_map_of_mem L.subtype hy))
    have hhL : y * v = v * y := Subtype.ext hh
    simpa only [map_mul] using congrArg f hhL

/-- Deduce clause (5) from the numerical bounds and the exact implication
16.5.7(1). The model bounds remain explicit until the catalogue is assembled. -/
theorem clause_five_of_bounds {T : Sylow 2 G} {L R : Subgroup G}
    (_hlarge : ExcludesLargeRankTwo L)
    (hne : star L (componentSylow T L) ≠ ⊥)
    (hindex : (star L (componentSylow T L)).relIndex (star L T) ≤ 2)
    (hcentral : Nat.card ↥(star L T ⊓ centralizer (star L (componentSylow T L) : Set _)) ≤ 2)
    (h57 : center L = ⊥ →
      Nat.card ↥(star L T ⊓ centralizer (star L (componentSylow T L) : Set _)) = 2 →
      (star L (componentSylow T L)).relIndex (star L T) ≤ 2 →
      ∀ r ∈ star L R, ¬ IsTwoCentralIn (star L L) r) :
    center L ≠ ⊥ ∨ ∀ r ∈ star L R, ¬ IsTwoCentralIn (star L L) r := by
  by_cases hZ : center L = ⊥
  · apply Or.inr
    apply h57 hZ _ hindex
    apply card_centralizer_eq_two _ _ (star_mono L inf_le_left) _ hne hcentral
    exact star_isPGroup L (T.isPGroup'.of_injective (inclusion inf_le_left)
      (inclusion_injective _))
  · exact Or.inl hZ
/-- Deduce clause (6), discharging the detector from 16.4.9(1) and avoidance
from clause (5) for every relative Sylow subgroup of every J in Δ₀.
Uniformity in this premise is an assembly obligation, not merely the claim
for the single initially chosen R. -/
theorem clause_six_of_clause_five
    {L X : Subgroup G} {g l u c v : G}
    (_hlarge : ExcludesLargeRankTwo L)
    (hZ : center L = ⊥)
    (hXL : X ≤ L) (hgX : g ∈ normalizer (X : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hc : c ∈ centralizer (L : Set G))
    (hv : v ∈ L) (hl : l ∈ L) (hucv : u = c * v)
    (hnormalizers : normalizer (centralizer (L : Set G) : Set G) =
      normalizer (L : Set G))
    (hsmall : ∀ J ∈ delta L, J ∉ deltaZero L →
      ∀ R : Subgroup G, SylowIn R
        (J ⊓ normalizer (centralizer (L : Set G) : Set G)) → Nat.card R = 2)
    (hfive : ∀ J ∈ deltaZero L, ∀ R : Subgroup G,
      SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)) →
      center L ≠ ⊥ ∨ ∀ r ∈ star L R, ¬ IsTwoCentralIn (star L L) r)
    (hw : v * MulAut.conj l v ∈ X) (hw2 : orderOf (v * MulAut.conj l v) = 2) :
    ¬ IsTwoCentralIn (L.conjBy g) (v * MulAut.conj l v) := by
  apply projected_product_not_twoCentral hZ hXL hgX hu hu2 hc hv hl hucv _ _ hw hw2
  · intro J hJ i hiJ hi2 hiKL hiK
    exact mem_deltaZero_of_inner_involution hnormalizers hsmall hJ hiJ hi2 hiKL hiK
  · intro J hJ i k w hiJ hiN hi2 hk hwL hi
    let D := J ⊓ normalizer (centralizer (L : Set G) : Set G)
    have hiD : i ∈ D := ⟨hiJ, hiN⟩
    have hiD2 : orderOf (⟨i, hiD⟩ : D) = 2 := by
      rwa [← orderOf_injective D.subtype D.subtype_injective]
    have hp : IsPGroup 2 (zpowers (⟨i, hiD⟩ : D)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hiD2, pow_one])
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    let R := (P : Subgroup D).map D.subtype
    have hR : SylowIn R D := ⟨P, rfl⟩
    have hiR : i ∈ R := ⟨⟨i, hiD⟩, hP (mem_zpowers _), rfl⟩
    have hno := (hfive J hJ R hR).resolve_left (fun hne => hne hZ)
    have hiNL : i ∈ normalizer (L : Set G) := hnormalizers ▸ hiN
    have hip : starProjection L ⟨i, hiNL⟩ ∈ star L R := ⟨⟨i, hiNL⟩, hiR, rfl⟩
    have hkN : k ∈ normalizer (L : Set G) := centralizer_le_normalizer _ hk
    have hkq : starProjection L ⟨k, hkN⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    have hiw : (⟨i, hiNL⟩ : normalizer (L : Set G)) =
        ⟨k, hkN⟩ * inclusion L.le_normalizer ⟨w, hwL⟩ := Subtype.ext hi
    have hq : starProjection L ⟨i, hiNL⟩ = componentProjection L ⟨w, hwL⟩ := by
      rw [hiw, map_mul, hkq, one_mul]
      rfl
    intro htwo
    have hinj : Function.Injective (componentProjection L) :=
      (MonoidHom.ker_eq_bot_iff _).mp ((componentProjection_ker L).trans hZ)
    have hmap := map_twoCentral (v := ⟨w, hwL⟩) (componentProjection L) hinj htwo
    rw [componentProjection_range] at hmap
    rw [hq] at hip
    exact hno _ hip hmap

end CFSG.Quasithin.Chapter16.Intersections.Catalogue
