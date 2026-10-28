module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource
public import Theory.GroupTheory.NormalizerImageCentralizer
public import Theory.GroupTheory.AbelianConjugateSpan
/-!
# The normal component-image branch of C.5.12

On the actual elementary module V containing U, the image of P₁ is
exactly the centralizer in the full Sylow image of L=⟨K^{N_X(P₁)}⟩.
The upper bound uses faithful action modulo O₂(KT), while the lower
bound propagates the proved block displacement [P₁,K]≤U through the
actual conjugate span. No equality between the centralizer kernel and
the two-core is assumed. If L's image is normal, its Sylow centralizer
is preserved and C.5.13 supplies the original normalizer conclusion.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl

private theorem commutes_of_ker_le {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G →* H) (g : G →* J) (hk : f.ker ≤ g.ker)
    {a b : G} (hc : f a * f b = f b * f a) : g a * g b = g b * g a := by
  have hm : (a*b)/(b*a) ∈ f.ker := by
    simp only [MonoidHom.mem_ker,map_div,map_mul,hc,div_self']
  have hmg : g ((a*b)/(b*a)) = 1 := hk hm
  simpa only [map_div,map_mul,div_eq_one] using hmg

open Theory.GroupTheory
theorem noncubic_image_centralizer_le_twoCore {G H : Type*} [Group G] [Group H] [Finite G]
    (K T : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = ⊤)
    (f : G →* H) (hker : f.ker ≤ pCore 2 G) :
    T.map f ⊓ centralizer (K.map f : Set H) ≤ (pCore 2 G).map f := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hf := noncubic_core_quotient_faithful K T hK hqK hT hsup
  rintro z ⟨⟨t,ht,rfl⟩,hc⟩
  have hq : q t ∈ T.map q ⊓ centralizer (K.map q : Set (G ⧸ pCore 2 G)) := by
    refine ⟨mem_map_of_mem q ht,?_⟩
    rintro _ ⟨k,hk,rfl⟩
    exact commutes_of_ker_le f q (by simpa only [q,QuotientGroup.ker_mk'] using hker)
      (hc (f k) (mem_map_of_mem f hk))
  rw [hf,mem_bot] at hq
  exact mem_map_of_mem f ((QuotientGroup.eq_one_iff t).mp hq)

open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.Section05
open ConjugateSource.RankOne
open scoped IsMulCommutative commutatorElement
theorem noncubic_action_centralizer_le_core {G : Type*} [Group G] [Finite G]
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V] :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    (T.subgroupOf X).map q ⊓ centralizer ((K.subgroupOf X).map q : Set _) ≤
      (((K ⊔ T).pCoreIn 2).subgroupOf X).map q := by
  let A := K ⊔ T
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let f := q.comp (inclusion hAX)
  have hker : f.ker ≤ pCore 2 A := by
    intro a ha
    have hc := (QuotientGroup.eq_one_iff _).mp ha
    have hu : (a : G) ∈ centralizer (U K : Set G) := by
      intro u hu
      exact congrArg X.subtype (hc ⟨u,hVX (hUV hu)⟩ (hUV hu))
    have hp : (a : G) ∈ A.pCoreIn 2 :=
      (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
        K T hK.chi.short hT hTK) ▸ ⟨a.property,hu⟩
    obtain ⟨b,hb,he⟩ := hp
    exact (Subtype.ext he : b=a) ▸ hb
  let K₀ := K.subgroupOf A
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  have hcomp : K₀.IsCComponent := (noncubic_mem_local_family K T hK h3 hTK P hP).1
  let e := (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  have hquasi : IsQuasisimple (K₀ ⧸ pCore 2 K₀) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hgen : K₀ ⊔ T.subgroupOf A = ⊤ := by
    change K.subgroupOf A ⊔ T.subgroupOf A = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hm (D : Subgroup G) (hDA : D ≤ A) :
      (D.subgroupOf A).map f = (D.subgroupOf X).map q := by
    rw [← Subgroup.map_map]
    congr 1
    apply map_injective X.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le (hDA.trans hAX)]
    exact map_subgroupOf_eq_of_le hDA
  have hf := noncubic_image_centralizer_le_twoCore K₀ (T.subgroupOf A)
    hcomp hquasi hT.comap_subtype hgen f hker
  change (T.subgroupOf A).map f ⊓ centralizer ((K.subgroupOf A).map f : Set _) ≤ _ at hf
  rw [hm T le_sup_right,hm K le_sup_left] at hf
  refine hf.trans_eq ?_
  change (pCore 2 A).map f = _
  rw [← Subgroup.map_map]
  congr 1
  apply map_injective X.subtype_injective
  rw [Subgroup.map_map,map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAX)]
  rfl

/-- The actual core image is the Sylow centralizer of the auxiliary block span. -/
theorem noncubic_core_image_eq_span_centralizer {G : Type*} [Group G] [Finite G]
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V] :
    let C := (K ⊔ T).pCoreIn 2
    let N := X ⊓ normalizer (C : Set G)
    let L := conjugateSpanBy K N
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    (C.subgroupOf X).map q =
      (T.subgroupOf X).map q ⊓ centralizer ((L.subgroupOf X).map q : Set _) := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  have hCX : C ≤ X := (pCoreIn_le 2 _).trans hAX
  have hCT : C ≤ T := (pCoreIn_le_sylow _ P).trans_eq hP
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have hLX : L ≤ X := conjugateSpanBy_le (le_sup_left.trans hAX)
    (inf_le_left.trans X.le_normalizer)
  have hKC : ⁅K,C⁆ ≤ U K := block_fixer_displacement hK.chi.short
    ((pCoreIn_le 2 _).trans (sup_le K.le_normalizer hTK))
    ((CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
      K T hK.chi.short hT hTK).symm.le.trans inf_le_right)
  have hCL : (C.subgroupOf X).map q ≤ centralizer ((L.subgroupOf X).map q : Set _) := by
    have hCK : (C.subgroupOf X).map q ≤ centralizer ((K.subgroupOf X).map q : Set _) := by
      rintro _ ⟨c,hc,rfl⟩ _ ⟨k,hk,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hv : ((⁅k,c⁆ : X) : G) ∈ V := hUV (hKC (commutator_mem_commutator hk hc))
      intro v hv'
      exact Subtype.ext (congrArg V.subtype
        (mul_comm (⟨v,hv'⟩ : V) ⟨⁅(k:G),(c:G)⁆,hv⟩))
    have hNC : (N.subgroupOf X).map q ≤ normalizer ((C.subgroupOf X).map q : Set _) := by
      apply (map_mono (f := q) ?_).trans (le_normalizer_map _)
      rw [← subgroupOf_normalizer_eq hCX]
      exact subgroupOf_mono X inf_le_right
    have hspan := le_centralizer_conjugateSpanBy_of_normalizes
      ((C.subgroupOf X).map q) ((K.subgroupOf X).map q) ((N.subgroupOf X).map q) hNC hCK
    have he : conjugateSpanBy (K.subgroupOf X) (N.subgroupOf X) = L.subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (le_sup_left.trans hAX),
        map_subgroupOf_eq_of_le (show N ≤ X from inf_le_left),map_subgroupOf_eq_of_le hLX]
    rwa [← map_conjugateSpanBy,he] at hspan
  apply le_antisymm (le_inf (map_mono (subgroupOf_mono X hCT)) hCL)
  exact (inf_le_inf_left _ (centralizer_le
    (map_mono (subgroupOf_mono X (le_conjugateSpanBy K N))))).trans
    (noncubic_action_centralizer_le_core K T X V hK h3 hT hTK P hP hAX hVX hXV hUV)


/-- The normal-image branch reduces the original C.5.12 bound to the
literal C.5.13 conclusion on N_X(P₁). -/
theorem noncubic_control_of_normal_span_image
    {G : Type*} [Group G] [Finite G]
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V]
    (hnormal : let C := (K ⊔ T).pCoreIn 2
      let L := conjugateSpanBy K (X ⊓ normalizer (C : Set G))
      let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
      ((L.subgroupOf X).map (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)))).Normal)
    (h513 : (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let C := (K ⊔ T).pCoreIn 2
  let L := conjugateSpanBy K (X ⊓ normalizer (C : Set G))
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let : ((L.subgroupOf X).map q).Normal := hnormal
  have hCX : C ≤ X := (pCoreIn_le 2 _).trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hCT : C ≤ T := (pCoreIn_le_sylow _ P).trans_eq hP
  have hk : T.subgroupOf X ⊓ q.ker ≤ C.subgroupOf X := by
    rintro t ⟨ht,hc⟩
    have hc' : t ∈ centralizer (V.subgroupOf X : Set X) := by
      exact (QuotientGroup.eq_one_iff t).mp hc
    have hu : (t : G) ∈ centralizer (U K : Set G) := by
      intro u hu
      exact congrArg X.subtype (hc' ⟨u,hVX (hUV hu)⟩ (hUV hu))
    change (t : G) ∈ (K ⊔ T).pCoreIn 2
    exact (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
      K T hK.chi.short hT hTK) ▸ ⟨mem_sup_right ht,hu⟩
  have he := noncubic_core_image_eq_span_centralizer K T X V hK h3 hT hTK
    P hP hAX hVX hXV hUV
  have hn := normalizer_le_of_image_centralizer q (T.subgroupOf X) (C.subgroupOf X)
    (subgroupOf_mono X hCT) hk ((L.subgroupOf X).map q) he
  rintro g ⟨hgX,hgT⟩
  have hg : (⟨g,hgX⟩ : X) ∈ normalizer (T.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hTX]
    exact hgT
  have hgC := hn hg
  rw [← subgroupOf_normalizer_eq hCX] at hgC
  exact h513 ⟨⟨hgX,hgC⟩,hgT⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
