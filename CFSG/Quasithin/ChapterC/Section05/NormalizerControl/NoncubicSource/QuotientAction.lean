module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Quotient
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.LocalFamily
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# The full Sylow action on the noncubic block image

Modulo the two-core, the quasisimple block is the generalized Fitting
subgroup of its two-group extension. Its centralizer is abelian and has
no nontrivial two-subgroup. This makes the original two-supplement faithful,
including on the literal auxiliary action quotient.
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G H : Type*} [Group G] [Group H] [Finite G]
private theorem quasisimple_two_supplement_faithful
    (K T : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = ⊤) (hcore : pCore 2 G = ⊥) :
    T ⊓ centralizer (K : Set G) = ⊥ := by
  let C := centralizer (K : Set G)
  have hquot : IsPGroup 2 (G ⧸ K) :=
    quotient_isPGroup_of_sup_eq_top T K hT (sup_comm K T ▸ hsup)
  have hCK : C ≤ K := by
    change centralizer (K : Set G) ≤ K
    rw [← generalizedFitting_eq_of_quasisimple_two_quotient K hquot hcore]
    exact centralizer_generalizedFitting_le G
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (centralizer_le hCK)
  let D := T ⊓ C
  have hD : D.subgroupOf C ≤ pCore 2 C := le_sSup ⟨inferInstance,
    (hT.to_le (show D ≤ T from inf_le_left)).comap_subtype⟩
  have hCN : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map C.subtype⟩
  have hh := (map_mono (f := C.subtype) hD).trans hCN
  rw [map_subgroupOf_eq_of_le (show D ≤ C from inf_le_right),hcore] at hh
  exact le_bot_iff.mp hh

/-- A full two-group supplement acts faithfully on the quasisimple block
image after taking the literal ambient two-core quotient. -/
theorem noncubic_core_quotient_faithful (K T : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 G)
    T.map q ⊓ centralizer (K.map q : Set (G ⧸ pCore 2 G)) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  let : IsQuasisimple (K ⧸ pCore 2 K) := hqK
  let : IsQuasisimple (K.map q) := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  let : (K.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  apply quasisimple_two_supplement_faithful (K.map q) (T.map q) (hT.map q)
  · rw [← Subgroup.map_sup,hsup,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · exact pCore_quotient_pCore_eq_bot 2

/-- The same faithful action is carried by any literal homomorphism whose
kernel is precisely the original two-core. -/
theorem noncubic_image_faithful (K T : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hT : IsPGroup 2 T) (hsup : K ⊔ T = ⊤)
    (f : G →* H) (hker : f.ker = pCore 2 G) :
    T.map f ⊓ centralizer (K.map f : Set H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  have he (g : G) : (e (q g) : H) = f g := rfl
  have hf := noncubic_core_quotient_faithful K T hK hqK hT hsup
  apply le_bot_iff.mp
  rintro z ⟨⟨t,ht,rfl⟩,hc⟩
  have hq : q t ∈ T.map q ⊓ centralizer (K.map q : Set (G ⧸ pCore 2 G)) := by
    refine ⟨mem_map_of_mem q ht,?_⟩
    rintro _ ⟨k,hk,rfl⟩
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul,Subgroup.coe_mul,he] using hc (f k) (mem_map_of_mem f hk)
  rw [hf,mem_bot] at hq
  rw [← he t,hq,map_one]
  rfl

open Stellmacher ConjugateSource.RankOne
/-- The original full Sylow remains Sylow on the auxiliary action quotient,
and acts faithfully on the actual block image. -/
theorem source_omega_quotient_sylow_action (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hfixed : ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := source_omega_span_of_noncentral_fixed K T X hK.chi.short hT hTK P hP hA hAX hfixed
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    (∃ B : Sylow 2 (N ⧸ centralizer (V.subgroupOf N : Set N)),
      (B : Subgroup _) = (T.subgroupOf N).map q) ∧
    (T.subgroupOf N).map q ≤ normalizer ((K.subgroupOf N).map q : Set _) ∧
    (T.subgroupOf N).map q ⊓ centralizer ((K.subgroupOf N).map q : Set _) = ⊥ := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := source_omega_span_of_noncentral_fixed K T X hK.chi.short hT hTK P hP hA hAX hfixed
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hTN : T ≤ N := le_sup_right.trans hAN
  have hKN : K ≤ N := le_sup_left.trans hAN
  obtain ⟨B,hB⟩ := Chapter1.IsSylowIn.restrict (show Chapter1.IsSylowIn 2 T X from ⟨S,hS⟩)
    hTN (show N ≤ X from inf_le_left)
  have hTB : T.subgroupOf N = (B : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hTN,hB]
  refine ⟨⟨B.mapSurjective (QuotientGroup.mk'_surjective _), by
    change (B : Subgroup N).map q = (T.subgroupOf N).map q
    exact congrArg (Subgroup.map q) hTB.symm⟩, ?_, ?_⟩
  · apply (map_mono (f := q) ?_).trans (le_normalizer_map _)
    rw [← subgroupOf_normalizer_eq hKN]
    exact subgroupOf_mono N hTK
  let f := q.comp (inclusion hAN)
  have hker : f.ker = pCore 2 A := by
    ext a
    constructor
    · intro ha
      have hc := (QuotientGroup.eq_one_iff _).mp ha
      have hu : (a : G) ∈ centralizer (U K : Set G) := by
        intro u hu
        exact congrArg N.subtype (hc ⟨u,hs.2.1 (hs.2.2.2.1 hu)⟩ (hs.2.2.2.1 hu))
      have hp : (a : G) ∈ A.pCoreIn 2 :=
        (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
          K T hK.chi.short hT hTK) ▸ ⟨a.property,hu⟩
      obtain ⟨b,hb,he⟩ := hp
      exact (Subtype.ext he : b=a) ▸ hb
    · intro ha
      apply (QuotientGroup.eq_one_iff _).mpr
      intro v hv
      exact Subtype.ext ((normalizer_core_omega_span A X T P hP hA hAX).2.2.1
        (mem_map_of_mem A.subtype ha) v hv)
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
      (D.subgroupOf A).map f = (D.subgroupOf N).map q := by
    rw [← Subgroup.map_map]
    congr 1
    apply map_injective N.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le (hDA.trans hAN)]
    exact map_subgroupOf_eq_of_le hDA
  have hf := noncubic_image_faithful K₀ (T.subgroupOf A) hcomp hquasi hT.comap_subtype hgen f hker
  change (T.subgroupOf A).map f ⊓ centralizer ((K.subgroupOf A).map f : Set _) = ⊥ at hf
  rwa [hm T le_sup_right,hm K le_sup_left] at hf
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
