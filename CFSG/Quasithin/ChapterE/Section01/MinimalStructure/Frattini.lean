module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterE.Section01.MinimalSupplement
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowImageIntersection

/-!
# Frattini structure of minimal supplements

For a minimal supplement K over a Sylow two-subgroup T, the preimage of
any normal two-subgroup of the actual quotient image has normal Sylow
intersection with T. Frattini's argument makes the intersection normalizer
cover the image; minimality then makes this normalizer all of K.
In particular, the preimage of the intrinsic two-core of the image is
2-closed. No ambient normality of K is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(2), printed p.211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Minimality in the intrinsic group: a subgroup containing the prescribed
Sylow subgroup and covering the quotient image is the whole supplement. -/
theorem IsMinimalSupplement.eq_top_of_map_eq_top {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (L : Subgroup K)
    (hT : T.subgroupOf K ≤ L)
    (hL : L.map ((QuotientGroup.mk' Y).subgroupMap K) = ⊤) : L = ⊤ := by
  have hLY : L.map K.subtype ⊔ Y = X ⊔ T := by
    apply le_antisymm (sup_le ((map_subtype_le L).trans h.1.2.1)
      (h.1.2.2 ▸ le_sup_right))
    rw [← h.1.2.2]
    refine sup_le ?_ le_sup_right
    intro k hk
    have hm : (QuotientGroup.mk' Y).subgroupMap K ⟨k, hk⟩ ∈
        L.map ((QuotientGroup.mk' Y).subgroupMap K) := by rw [hL]; trivial
    obtain ⟨l, hl, he⟩ := hm
    have he' : QuotientGroup.mk' Y (l : G) = QuotientGroup.mk' Y k :=
      congrArg Subtype.val he
    have hy : (l : G)⁻¹ * k ∈ Y := QuotientGroup.eq.mp he'
    have hl' : (l : G) ∈ L.map K.subtype ⊔ Y :=
      (show L.map K.subtype ≤ L.map K.subtype ⊔ Y from le_sup_left) ⟨l, hl, rfl⟩
    have hy' : (l : G)⁻¹ * k ∈ L.map K.subtype ⊔ Y :=
      (show Y ≤ L.map K.subtype ⊔ Y from le_sup_right) hy
    simpa using (L.map K.subtype ⊔ Y).mul_mem hl' hy'
  have hKL : K ≤ L.map K.subtype := h.2
    ⟨(fun t ht => ⟨⟨t, h.1.1 ht⟩, hT ht, rfl⟩),
      (map_subtype_le L).trans h.1.2.1, hLY⟩ (map_subtype_le L)
  apply top_le_iff.mp
  intro k _
  obtain ⟨l, hl, he⟩ := hKL k.property
  exact (Subtype.ext he : l = k) ▸ hl

/-- The Sylow intersection with the preimage of any normal two-subgroup of
the quotient image is normal in the whole minimal supplement. -/
theorem IsMinimalSupplement.normal_inf_preimage (T : Sylow 2 G) {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    ∀ (C : Subgroup (K.map (QuotientGroup.mk' Y))) [C.Normal],
      IsPGroup 2 C →
      ((T : Subgroup G).subgroupOf K ⊓
        C.comap ((QuotientGroup.mk' Y).subgroupMap K)).Normal := by
  intro C _ hCp
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let S : Sylow 2 K := T.subtype h.1.1
  let Z := C.comap f
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal Z
  let B := (P : Subgroup Z).map Z.subtype
  have hB : B = (S : Subgroup K) ⊓ Z := by
    rw [show B = (P : Subgroup Z).map Z.subtype from rfl, hP, subgroupOf_map_subtype]
  let N := normalizer (B : Set K)
  have hSN : (S : Subgroup K) ≤ N := by
    rw [show N = normalizer (B : Set K) from rfl, hB]
    exact (le_inf le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hC : C ≤ (S : Subgroup K).map f :=
    hCp.le_sylow_of_normal (S.mapSurjective hf)
  have hBf : B.map f = C := by
    rw [S.map_image_eq_inf Z B P rfl (hB ▸ inf_le_left) f,
      map_comap_eq_self_of_surjective hf, inf_eq_right.mpr hC]
  have hNZ : N ⊔ Z = ⊤ := P.normalizer_sup_eq_top
  have hNf : N.map f = ⊤ := by
    have he := congrArg (Subgroup.map f) hNZ
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective hf, map_top_of_surjective f hf] at he
    have hCN : C ≤ N.map f := hBf ▸ map_mono (show B ≤ N from le_normalizer)
    rwa [sup_eq_left.mpr hCN] at he
  have hNtop : N = ⊤ := h.eq_top_of_map_eq_top N hSN hNf
  have hBn : B.Normal := normalizer_eq_top_iff.mp hNtop
  simpa only [hB, S, Sylow.coe_subtype, Z, f] using hBn

/-- The preimage of a normal two-subgroup of the actual image is 2-closed. -/
theorem IsMinimalSupplement.twoClosed_preimage (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (C : Subgroup (K.map (QuotientGroup.mk' Y))) [C.Normal]
    (hC : IsPGroup 2 C) :
    IsTwoClosed (C.comap ((QuotientGroup.mk' Y).subgroupMap K)) := by
  let Z := C.comap ((QuotientGroup.mk' Y).subgroupMap K)
  obtain ⟨P, hP⟩ := (T.subtype h.1.1).exists_subgroupOf_eq_of_normal Z
  have hn := h.normal_inf_preimage T C hC
  have hm : ((P : Subgroup Z).map Z.subtype).Normal := by
    simpa only [hP, subgroupOf_map_subtype, Sylow.coe_subtype, Z] using hn
  exact ⟨P, hm.of_map_subtype⟩

/-- E.1.10(2): the preimage in K of O₂(Kbar) is 2-closed.
The two-core is intrinsic to Kbar, the actual image of K in G/Y. -/
theorem IsMinimalSupplement.twoClosed_preimage_twoCore (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    IsTwoClosed ((pCore 2 (K.map (QuotientGroup.mk' Y))).comap
      ((QuotientGroup.mk' Y).subgroupMap K)) :=
  h.twoClosed_preimage T _ pCore_isPGroup

/-- In particular the kernel KY, regarded as a subgroup of K, is 2-closed. -/
theorem IsMinimalSupplement.twoClosed_kernel (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    IsTwoClosed (Y.subgroupOf K) := by
  have ht := h.twoClosed_preimage T ⊥ IsPGroup.of_bot
  have he : (⊥ : Subgroup (K.map (QuotientGroup.mk' Y))).comap
      ((QuotientGroup.mk' Y).subgroupMap K) = Y.subgroupOf K := by
    ext k
    change ((QuotientGroup.mk' Y).subgroupMap K k = 1) ↔ (k : G) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : G)
  rwa [he] at ht

end CFSG.Quasithin.ChapterE
