module

public import CFSG.Quasithin.Chapter16.Section04To05.RelativeSylow
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Relative Sylow transport for the intersection setup

Sylow conjugacy inside H = N_G(C_G(L)) moves a Sylow subgroup of
N_{K'}(K) into the fixed T. Conjugating by an element of H preserves Δ.
This constructs Notation 16.4.1 from nonemptiness of Δ, without assuming
that an arbitrary preselected K' already has its relative Sylow in T.

The relative Sylow restriction lemma keeps normality inside the specified
overgroup. These transports are also used in Lemma 16.4.2(4),(6).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1183.
Conjugation is left conjugation throughout.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem SylowIn.of_maximal {R H : Subgroup G} (hp : IsPGroup 2 R)
    (hle : R ≤ H) (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H → R ≤ Q → Q = R) :
    SylowIn R H := by
  obtain ⟨S, hS⟩ := (hp.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  refine ⟨S, hmax _ (S.isPGroup'.map _) (map_subtype_le _) ?_⟩
  rw [← map_subgroupOf_eq_of_le hle]
  exact map_mono hS

theorem SylowIn.inf_normal {R H N : Subgroup G} (h : SylowIn R H)
    (hle : N ≤ H) (hn : H ≤ normalizer (N : Set G)) : SylowIn (R ⊓ N) N := by
  obtain ⟨S, rfl⟩ := h
  let : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hle).mpr hn
  obtain ⟨P, hP⟩ := S.exists_sylow_map_eq_inf_of_normal (N.subgroupOf H)
  let e := subgroupOfEquivOfLe hle
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((P : Subgroup _).map e.toMonoidHom).map N.subtype = _
  rw [map_map]
  have hh := congrArg (Subgroup.map H.subtype) hP
  rw [map_map, map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hle] at hh
  exact hh

theorem SylowIn.exists_le_conjugate {R H Q : Subgroup G}
    (h : SylowIn R H) (hp : IsPGroup 2 Q) (hle : Q ≤ H) :
    ∃ a ∈ H, Q ≤ R.conjBy a := by
  obtain ⟨a, ha, hQ⟩ := h.exists_conjugate_le hp hle
  refine ⟨a⁻¹, H.inv_mem ha, ?_⟩
  have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hQ
  change (Q.conjBy a).conjBy a⁻¹ ≤ R.conjBy a⁻¹ at hh
  simpa only [conjBy_inv] using hh

theorem SylowIn.ne_bot_of_even {R H : Subgroup G}
    (h : SylowIn R H) (he : Even (Nat.card H)) : R ≠ ⊥ := by
  obtain ⟨S, rfl⟩ := h
  intro hb
  have hS : (S : Subgroup H) = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb
  have hn := S.not_dvd_index
  rw [hS, index_bot] at hn
  exact hn (even_iff_two_dvd.mp he)

variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem StandardSetup.sylowIn_normalizer (h : StandardSetup T z L) :
    SylowIn (T : Subgroup G) (normalizer (centralizer (L : Set G) : Set G)) := by
  have hle := h.normalizers_eq ▸ h.sylow_normalizes
  refine ⟨T.subtype hle, ?_⟩
  exact map_subgroupOf_eq_of_le hle

theorem StandardSetup.commutingSylow_sylow (h : StandardSetup T z L) :
    SylowIn (commutingSylow T L) (centralizer (L : Set G)) :=
  h.sylowIn_normalizer.inf_normal le_normalizer le_rfl

omit [Finite G] in
theorem delta_conjugate
    {J : Subgroup G} (hJ : J ∈ delta L) {a : G}
    (ha : a ∈ normalizer (centralizer (L : Set G) : Set G)) :
    J.conjBy a ∈ delta L := by
  obtain ⟨⟨g, rfl⟩, hne, hev⟩ := hJ
  have hK : (centralizer (L : Set G)).conjBy a⁻¹ = centralizer (L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (centralizer (L : Set G) : Set G)).inv_mem ha)
  have hN := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (centralizer (L : Set G) : Set G)).le_normalizer ha)
  change (normalizer (centralizer (L : Set G) : Set G)).map
    (MulAut.conj a).toMonoidHom = _ at hN
  refine ⟨⟨a * g, (conjBy_conjBy _ _ _ )⟩, ?_, ?_⟩
  · intro he
    have he' := congrArg (fun X : Subgroup G => X.conjBy a⁻¹) he
    exact hne (by simpa only [conjBy_inv, hK] using he')
  · have he := card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
      (K := (centralizer (L : Set G)).conjBy g ⊓
        normalizer (centralizer (L : Set G) : Set G)) (MulAut.conj a).injective
    rw [map_inf _ _ _ (MulAut.conj a).injective, hN] at he
    exact he.symm ▸ hev

theorem StandardSetup.exists_intersectionSetup (h : StandardSetup T z L)
    (hne : (delta L).Nonempty) : ∃ g R, IntersectionSetup T z L g R := by
  obtain ⟨J, hJ⟩ := hne
  obtain ⟨g, hg⟩ := hJ.1
  let H := J ⊓ normalizer (centralizer (L : Set G) : Set G)
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := H)
  let R := (P : Subgroup H).map H.subtype
  have hR : SylowIn R H := ⟨P, rfl⟩
  obtain ⟨a, ha, hle⟩ := h.sylowIn_normalizer.exists_conjugate_le
    hR.isPGroup (hR.le.trans inf_le_right)
  have hN := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (centralizer (L : Set G) : Set G)).le_normalizer ha)
  change (normalizer (centralizer (L : Set G) : Set G)).map
    (MulAut.conj a).toMonoidHom = _ at hN
  refine ⟨a * g, R.conjBy a, h, ?_, ?_, hle⟩
  · have hd := delta_conjugate hJ ha
    simpa only [hg, conjBy_conjBy] using hd
  · have hm := hR.map (MulAut.conj a)
    change SylowIn (R.conjBy a) (H.conjBy a) at hm
    change SylowIn _ ((J ⊓ normalizer (centralizer (L : Set G) : Set G)).conjBy a) at hm
    change SylowIn _ ((J ⊓ normalizer (centralizer (L : Set G) : Set G)).map _) at hm
    rw [map_inf _ _ _ (MulAut.conj a).injective, hN] at hm
    change SylowIn (R.conjBy a) (J.conjBy a ⊓ _) at hm
    simpa only [hg, conjBy_conjBy] using hm

end CFSG.Quasithin.Chapter16.Intersections
