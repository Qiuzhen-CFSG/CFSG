module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponent
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NormalImage
public import Theory.SpecificGroups.PSL2.PrimePerfectCentralizer
public import CFSG.Quasithin.ClassicalModels
/-!
# The prime-field component branch of C.5.12

The actual auxiliary image is a nontrivial perfect subgroup of the normal
full span image. If that span has a prime-field PSL₂ model, its centralizer
equals the auxiliary image centralizer. Thus the literal core image is the
intersection of the Sylow image with a normal centralizer. The exact quotient
kernel bound lifts its normalizer control and the earlier C.5.13 conclusion.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

theorem noncubic_prime_component_control
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V]
    (hshort : IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))))
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hmodel : let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
      let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
      ClassicalGroup.IsPSL (((conjugateSpanBy K X).subgroupOf X).map q) 2 p)
    (h513 : (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let B := (L.subgroupOf X).map q
  let Pstar := (C.subgroupOf X).map q
  have hcomp := noncubic_auxiliary_image_isComponent K T X V hK h3 hT
    hUT hTK P hP hA hAX S hS hVX hXV hUV hshort
  have hBC := hcomp.1
  let Hc := centralizer (Pstar : Set (X ⧸ centralizer (V.subgroupOf X : Set X)))
  let : IsQuasisimple (B.subgroupOf Hc) := hcomp.2.2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBC)
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  have hBne : B ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot B).mp inferInstance
  let D0 := conjugateSpanBy K X
  have hD0X : D0 ≤ X := conjugateSpanBy_le_self (le_sup_left.trans hAX)
  let : (D0.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hD0X).mpr
    (le_normalizer_conjugateSpanBy K X)
  let D := (D0.subgroupOf X).map q
  let : D.Normal := by dsimp [D]; infer_instance
  have hBD : B ≤ D := map_mono (subgroupOf_mono X (conjugateSpanBy_mono le_rfl inf_le_left))
  obtain ⟨F,_,_,hF,⟨eD⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  have hc : centralizer (B : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) =
      centralizer (D : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) :=
    Theory.PSL2.centralizer_eq_of_perfect_in_prime_component D B hBne hBD hlarge hF eD
  have hCX : C ≤ X := (pCoreIn_le 2 _).trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hCT : C ≤ T := (pCoreIn_le_sylow _ P).trans_eq hP
  have hk : T.subgroupOf X ⊓ q.ker ≤ C.subgroupOf X := by
    rintro t ⟨ht,hc'⟩
    have hc'' : t ∈ centralizer (V.subgroupOf X : Set X) :=
      (QuotientGroup.eq_one_iff t).mp hc'
    have hu : (t : G) ∈ centralizer (U K : Set G) := by
      intro u hu
      exact congrArg X.subtype (hc'' ⟨u,hVX (hUV hu)⟩ (hUV hu))
    change (t : G) ∈ (K ⊔ T).pCoreIn 2
    exact (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
      K T hK.chi.short hT hTK) ▸ ⟨mem_sup_right ht,hu⟩
  have he := noncubic_core_image_eq_span_centralizer K T X V hK h3 hT hTK
    P hP hAX hVX hXV hUV
  change (C.subgroupOf X).map q = (T.subgroupOf X).map q ⊓ centralizer (B : Set _) at he
  rw [hc] at he
  have hn := normalizer_le_of_image_centralizer q (T.subgroupOf X) (C.subgroupOf X)
    (subgroupOf_mono X hCT) hk D he
  rintro g ⟨hgX,hgT⟩
  have hg : (⟨g,hgX⟩ : X) ∈ normalizer (T.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hTX]
    exact hgT
  have hgC := hn hg
  rw [← subgroupOf_normalizer_eq hCX] at hgC
  exact h513 ⟨⟨hgX,hgC⟩,hgT⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
