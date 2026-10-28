module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.OmegaSpan

/-!
# Orders in the literal cubic source quotient

The C.5.11 Sylow subgroup restricts to N_X(P₁), and its image modulo
the centralizer of the constructed omega-center span has order two.
The original A₃ block has image of order three: its two-core is killed,
while its image cannot be trivial because [U₁,K₁]=U₁ is nontrivial.
These are the exact quotient groups used by the cubic transvection
argument in Aschbacher–Smith C.5.13, printed p.162.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem centralizer_subgroupOf_image (X V : Subgroup G) (hVX : V ≤ X) :
    (centralizer (V.subgroupOf X : Set X)).map X.subtype = X ⊓ centralizer (V : Set G) := by
  ext g
  constructor
  · rintro ⟨g,hg,rfl⟩
    refine ⟨g.property,?_⟩
    intro v hv
    exact congrArg X.subtype (hg ⟨v,hVX hv⟩ hv)
  · rintro ⟨hgX,hgV⟩
    refine ⟨⟨g,hgX⟩,?_,rfl⟩
    intro v hv
    exact Subtype.ext (hgV v hv)

/-- The source Sylow index is the actual order of the faithful action Sylow. -/
theorem quotient_sylow_card_of_centralizer_index
    (X V T : Subgroup G) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T)
    (hi : (T ⊓ centralizer (V : Set G)).relIndex T = 2) :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    Nat.card (P.mapSurjective (QuotientGroup.mk'_surjective
      (centralizer (V.subgroupOf X : Set X)))) = 2 := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let C := centralizer (V.subgroupOf X : Set X)
  let q := QuotientGroup.mk' C
  dsimp only
  change Nat.card ((P : Subgroup X).map q) = 2
  rw [← relIndex_ker,QuotientGroup.ker_mk']
  have hh := relIndex_map_map_of_injective C (P : Subgroup X) X.subtype_injective
  rw [centralizer_subgroupOf_image X V hVX,hP] at hh
  have hTX : T ≤ X := hP ▸ map_subtype_le _
  have he : (X ⊓ centralizer (V : Set G)).relIndex T =
      (T ⊓ centralizer (V : Set G)).relIndex T := by
    rw [← inf_relIndex_right (X ⊓ centralizer (V : Set G)) T]
    congr 1
    ext g
    constructor
    · exact fun hg => ⟨hg.2,hg.1.2⟩
    · exact fun hg => ⟨⟨hTX hg.1,hg.2⟩,hg.1⟩
  exact hh.symm.trans (he.trans hi)
private theorem sylow_in_intermediate
    (X Y T : Subgroup G) (hYX : Y ≤ X) (hTY : T ≤ Y)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    ∃ Q : Sylow 2 Y, (Q : Subgroup Y).map Y.subtype = T := by
  have hPY : (P : Subgroup X) ≤ Y.subgroupOf X := by
    intro p hp
    exact hTY (hP ▸ mem_map_of_mem X.subtype hp)
  let S := P.subtype hPY
  let e := subgroupOfEquivOfLe hYX
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q,?_⟩
  change ((S : Subgroup (Y.subgroupOf X)).map e.toMonoidHom).map Y.subtype = T
  rw [Subgroup.map_map]
  change (S : Subgroup (Y.subgroupOf X)).map (X.subtype.comp (Y.subgroupOf X).subtype) = T
  rw [← Subgroup.map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPY,hP]

open ConjugateSource.RankOne
/-- C.5.11 and the actual omega-center span construct the order-two Sylow
subgroup of X₁/C_X₁(V₁) used in the A₃ branch. -/
theorem alternating_three_source_quotient_sylow
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hcore : T ⊓ centralizer (U K : Set G) = (K ⊔ T).pCoreIn 2)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let X₁ := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
    let hp := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
    let : (V₁.subgroupOf X₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hp.2.1).mpr hp.2.2.1
    ∃ Q : Sylow 2 (X₁ ⧸ centralizer (V₁.subgroupOf X₁ : Set X₁)), Nat.card Q = 2 := by
  let A := K ⊔ T
  let X₁ := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
  obtain ⟨_he,hVX,hXV,_hUV,_hVT,hCV⟩ := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
  have hAX₁ : A ≤ X₁ := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  obtain ⟨P₁,hP₁⟩ := sylow_in_intermediate X X₁ T inf_le_left (le_sup_right.trans hAX₁) PX hPX
  have hi : (T ⊓ centralizer (V₁ : Set G)).relIndex T = 2 := by
    rw [hCV,← hcore]
    exact alternating_three_sylow_action_index h ha hT hTK hx hnc
  let : (V₁.subgroupOf X₁).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  refine ⟨P₁.mapSurjective (QuotientGroup.mk'_surjective _),?_⟩
  exact quotient_sylow_card_of_centralizer_index X₁ V₁ T hVX hXV P₁ hP₁ hi
/-- The original A₃ block has its actual cubic image on every source span
containing U and centralized by the core of KT. -/
theorem alternating_three_quotient_image_card
    (K T X V : Subgroup G) (ha : ChapterC.IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X)
    (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) (hCV : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G)) :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    Nat.card ((K.subgroupOf X).map
      (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)))) = 3 := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let C := centralizer (V.subgroupOf X : Set X)
  let q := QuotientGroup.mk' C
  have hKX : K ≤ X := le_sup_left.trans hAX
  let f := q.comp (inclusion hKX)
  have hr : f.range = (K.subgroupOf X).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    apply Subtype.ext
    exact hCV (pCoreIn_mono_of_normalizes (show K ≤ K ⊔ T from le_sup_left)
      (sup_le K.le_normalizer hTK) (mem_map_of_mem K.subtype hk)) v hv
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    obtain ⟨e⟩ := ha.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd : Nat.card f.range ∣ 3 := by
    have hh := index_dvd_of_le hk
    rw [index_ker] at hh
    exact hc ▸ hh
  have hne : f.range ≠ ⊥ := by
    intro he
    have hKC : K ≤ centralizer (U K : Set G) := by
      intro k hk u hu
      have hh : f ⟨k,hk⟩ = 1 := by
        have hm : f ⟨k,hk⟩ ∈ f.range := ⟨⟨k,hk⟩,rfl⟩
        simpa only [he,mem_bot] using hm
      have hh' : (⟨k,hKX hk⟩ : X) ∈ C := (QuotientGroup.eq_one_iff _).mp hh
      exact congrArg X.subtype (hh' ⟨u,hVX (hUV hu)⟩ (hUV hu))
    have hshort := ha.2.1
    have hUK : ⁅U K,K⁆ = U K := by
      have hh := commutator_isPPerfect_idempotent (⊤ : Subgroup K) (pCore 2 K)
        (hshort.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
          (topEquiv (G := K)).symm.surjective) pCore_isPGroup le_normalizer_of_normal
      have hm := congrArg (map K.subtype) hh
      simpa only [U,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hm
    have hz : U K = ⊥ := hUK.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKC))
    exact hshort.blockU_ne_bot ((map_injective K.subtype_injective)
      (by simpa only [U,Subgroup.map_bot] using hz))
  have hcardne : Nat.card f.range ≠ 1 := fun he => hne (card_eq_one.mp he)
  dsimp only
  change Nat.card ((K.subgroupOf X).map q) = 3
  rw [← hr]
  exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd |>.resolve_left hcardne
/-- Both orders in the literal C.5.13 quotient are obtained from the source
span, the original A₃ block, and the C.5.11 Sylow subgroup. -/
theorem alternating_three_source_quotient_orders
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hcore : T ⊓ centralizer (U K : Set G) = (K ⊔ T).pCoreIn 2)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let X₁ := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
    let hp := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
    let : (V₁.subgroupOf X₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hp.2.1).mpr hp.2.2.1
    ∃ Q : Sylow 2 (X₁ ⧸ centralizer (V₁.subgroupOf X₁ : Set X₁)), Nat.card Q = 2 ∧
      Nat.card ((K.subgroupOf X₁).map
        (QuotientGroup.mk' (centralizer (V₁.subgroupOf X₁ : Set X₁)))) = 3 := by
  let A := K ⊔ T
  let X₁ := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
  obtain ⟨_he,hVX,hXV,hUV,_hVT,_hCV⟩ := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
  have hAX₁ : A ≤ X₁ := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hCV := (normalizer_core_omega_span A X T P hP hA hAX).2.2.1
  let : (V₁.subgroupOf X₁).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  obtain ⟨Q,hQ⟩ := alternating_three_source_quotient_sylow h ha hT hTK P hP hA X hAX hcore PX hPX hx hnc
  exact ⟨Q,hQ,alternating_three_quotient_image_card K T X₁ V₁ ha hTK hAX₁ hVX hXV hUV hCV⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
