module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal

/-!
# The Sylow bridge for uniform exclusion of inner involutions

The terminal use of 16.5.6(5) quantifies over every J in Δ₀ and every
inner involution of J, whereas the local arguments fix a Sylow T.
Put the involution in a Sylow subgroup of J ∩ N_G(K), then conjugate
that subgroup into T inside N_G(K) = N_G(L). This preserves L, K,
the inner factorization, and two-centrality. The detector 16.4.9(3)
places the resulting conjugate back in Δ₀.

The last theorem supplies this change of quantifiers, conditional on
the local exclusion and the genuine earlier detector. It does not assert
the local exclusion, which is the remaining content of 16.5.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1189, 1197, 1201–1203. Conjugation is left conjugation.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Transport a relative Sylow subgroup under an ambient automorphism. -/
theorem SylowIn.map {R H : Subgroup G} (h : SylowIn R H) (e : G ≃* G) :
    SylowIn (R.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨S.mapSurjective (f := (e.subgroupMap H).toMonoidHom) (e.subgroupMap H).surjective, ?_⟩
  change ((S : Subgroup H).map (e.subgroupMap H).toMonoidHom).map
    (H.map e.toMonoidHom).subtype = _
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨(e.subgroupMap H) s, ⟨s, hs, rfl⟩, rfl⟩

/-- Two-centrality in L is invariant under N_G(L). -/
theorem IsTwoCentralIn.conj {L : Subgroup G} {v a : G}
    (h : IsTwoCentralIn L v) (ha : a ∈ normalizer (L : Set G)) :
    IsTwoCentralIn L (MulAut.conj a v) := by
  obtain ⟨hv2, S, hS, hv, hc⟩ := h
  have hL : L.map (MulAut.conj a).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp ha
  refine ⟨(MulAut.conj a).orderOf_eq v |>.trans hv2,
    S.conjBy a, hL ▸ hS.map (MulAut.conj a), mem_map_of_mem _ hv, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
    congrArg (MulAut.conj a) (mem_centralizer_singleton_iff.mp (hc hs))

/-- Conjugate a relative Sylow into T while staying in its overgroup N. -/
theorem SylowIn.exists_conj_le {R H N : Subgroup G} (h : SylowIn R H)
    (hHN : H ≤ N) (T : Sylow 2 G) (hTN : (T : Subgroup G) ≤ N) :
    ∃ a ∈ N, R.conjBy a ≤ (T : Subgroup G) := by
  have hRN := h.le.trans hHN
  obtain ⟨Q, hQ⟩ := (h.isPGroup.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq N Q (T.subtype hTN)
  refine ⟨a, a.property, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have hm : (MulAut.conj a) (⟨r, hRN hr⟩ : N) ∈ (a • Q : Sylow 2 N) :=
    mem_map_of_mem _ (hQ hr)
  rw [ha] at hm
  exact hm

/-- A nonidentity projection property invariant under N_G(L) can be
excluded uniformly by proving the exclusion with the relative Sylow in T.
This also applies to root classes during the Sp₄ argument. -/
theorem no_projection_property_of_sylow_exclusion
    {L : Subgroup G} (T : Sylow 2 G) (bad : G → Prop)
    (hbad1 : ∀ w, bad w → w ≠ 1)
    (hbad_conj : ∀ a ∈ normalizer (L : Set G), ∀ w, bad w → bad (MulAut.conj a w))
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNK : normalizer (centralizer (L : Set G) : Set G) =
      normalizer (L : Set G))
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hdetect : ∀ J : Subgroup G,
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L)
    (hlocal : ∀ J ∈ deltaZero L, ∀ R : Subgroup G,
      SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)) →
      R ≤ (T : Subgroup G) → ∀ i k w : G,
      i ∈ R → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ bad w) :
    ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ bad w := by
  intro J hJ i k w hi hi2 hk hw hik hcentral
  let K := centralizer (L : Set G)
  let N := normalizer (K : Set G)
  let H := J ⊓ N
  have hiN : i ∈ N := by
    rw [hik]
    apply N.mul_mem
    · exact K.le_normalizer hk
    · change w ∈ normalizer (centralizer (L : Set G) : Set G)
      rw [hNK]
      exact L.le_normalizer hw
  have hiH : i ∈ H := ⟨hi, hiN⟩
  have hiH2 : orderOf (⟨i, hiH⟩ : H) = 2 := by
    rwa [← orderOf_injective H.subtype H.subtype_injective]
  have hp : IsPGroup 2 (zpowers (⟨i, hiH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hiH2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let R := (S : Subgroup H).map H.subtype
  have hR : SylowIn R H := ⟨S, rfl⟩
  have hiR : i ∈ R := ⟨⟨i, hiH⟩, hS (mem_zpowers _), rfl⟩
  obtain ⟨a, haN, haR⟩ := hR.exists_conj_le (N := N) inf_le_right T (by simpa only [N, K, hNK] using hTN)
  let e := MulAut.conj a
  have haL : a ∈ normalizer (L : Set G) := hNK ▸ haN
  have hk' : e k ∈ K := (mem_normalizer_iff.mp haN k).mp hk
  have hw' : e w ∈ L := (mem_normalizer_iff.mp haL w).mp hw
  have hi' : e i ∈ J.conjBy a := mem_map_of_mem _ hi
  have hi2' : orderOf (e i) = 2 := (e.orderOf_eq i).trans hi2
  have hik' : e i = e k * e w := by rw [hik, map_mul]
  have hw1 : e w ≠ 1 := by
    intro he
    have hw1 := e.injective (he.trans (map_one e).symm)
    exact hbad1 w hcentral hw1
  have hiK : e i ∉ K := by
    intro hiK
    have hwK : e w ∈ K := by
      have hh := K.mul_mem (K.inv_mem hk') hiK
      simpa only [hik', inv_mul_cancel_left] using hh
    exact hw1 (Subgroup.disjoint_def.mp hdisjoint hw' hwK)
  have hJ' : J.conjBy a ∈ deltaZero L := by
    apply hdetect _ _ (e i) hi' hi2' (hik' ▸ mul_mem_sup hk' hw') hiK
    obtain ⟨b, hb⟩ := hJ.1.1
    exact ⟨a * b, by rw [hb, conjBy_conjBy]⟩
  have hN : N.map e.toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (N.le_normalizer haN)
  have hR' : SylowIn (R.conjBy a) (J.conjBy a ⊓ N) := by
    have hh := hR.map e
    change SylowIn _ ((J ⊓ N).map e.toMonoidHom) at hh
    rwa [map_inf _ _ _ e.injective, hN] at hh
  exact hlocal _ hJ' _ hR' haR (e i) (e k) (e w)
    (mem_map_of_mem _ hiR) hi2' hk' hw' hik' (hbad_conj a haL w hcentral)

/-- The local two-central exclusions imply the full quantifier required
by 16.5.6(5), even for involutions outside the initially chosen Sylow. -/
theorem no_twoCentral_projection_of_sylow_exclusion
    {L : Subgroup G} (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNK : normalizer (centralizer (L : Set G) : Set G) =
      normalizer (L : Set G))
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hdetect : ∀ J : Subgroup G,
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L)
    (hlocal : ∀ J ∈ deltaZero L, ∀ R : Subgroup G,
      SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)) →
      R ≤ (T : Subgroup G) → ∀ i k w : G,
      i ∈ R → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w) :
    ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w := by
  apply no_projection_property_of_sylow_exclusion T (IsTwoCentralIn L) _ _
    hTN hNK hdisjoint hdetect hlocal
  · intro w hw he
    simpa [he] using hw.1
  · intro a ha w hw
    exact hw.conj ha

end CFSG.Quasithin.Chapter16.Intersections
