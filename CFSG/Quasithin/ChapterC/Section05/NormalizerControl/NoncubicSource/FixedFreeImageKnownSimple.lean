module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenKnownSimple
/-!
# Known-simple source FixedFreeImage

The actual ordinary and exceptional A₇ blocks have trivial fixed layer. Their literal images in X/O₂(X) are normal by the proved known-simple A₇ containing-component theorem. The canonical map to X/C_X(V) retains the original two-core kernel and transports that normality.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02.LocalModels
universe u
theorem noncubic_a7_source_image_normal_knownSimple {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (htype : let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
      IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    let V := conjugateSpanBy (U K) X
    let hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans (le_sup_left.trans hAX))
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr (le_normalizer_conjugateSpanBy _ _)
    ((L.subgroupOf X).map (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)))).Normal := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
    let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
    exact conjugateSpanBy_elementary_of_commutative (U K) X
  have hL : IsShort L := htype.elim (fun h => h.2.1) And.left
  have hz : blockFixed L = ⊥ := htype.elim (fun h => h.seven_fixed_eq_bot) (fun h => h.fixed_eq_bot)
  have hm : IsAlternating (L ⧸ pCore 2 L) 7 := htype.elim (fun h => h.2.2.quotient_iso) (fun h => h.2.1)
  have hlocal := EmbeddingSelection.source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS
  have hLX : L ≤ X := hlocal.1.1
  have hTL : T ≤ normalizer (L : Set G) := hlocal.2
  have hUV : U L ≤ V := noncubic_auxiliary_blockU_le_source_module K T X V hK h3 hT hUT hTK P hP hA hAX S hS hXV (le_conjugateSpanBy _ _)
  have hVT : V ≤ T := by
    intro v hv
    have hc : (⟨v,hVX hv⟩ : X) ∈ pCore 2 X := hr.le_pCore hv
    exact hS ▸ mem_map_of_mem X.subtype (pCore_isPGroup.le_sylow_of_normal S hc)
  have hVL : ⁅V,L⁆ ≤ U L := by
    rw [commutator_comm]
    apply block_fixer_displacement hL (hVT.trans hTL)
    intro v hv u hu
    exact congrArg V.subtype (mul_comm (⟨u,hUV hu⟩ : V) ⟨v,hv⟩)
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  obtain ⟨eL⟩ := short_fixedFree_centralizer_image_equiv L X V hL hLX hVX hXV hUV hVL hz
  have hc := noncubic_full_span_kernel K T X hK h3 hUT hT hTK hKX hX S hS hVC
  have hLD : L ≤ D := conjugateSpanBy_mono le_rfl inf_le_left
  have hcL : ⁅pCore 2 X,L.subgroupOf X⁆ ≤ V.subgroupOf X :=
    (commutator_mono le_rfl (subgroupOf_mono X hLD)).trans hc.1.le
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (L.subgroupOf X).map r
  let φ := twoCoreToCentralizer (V.subgroupOf X) hr
  have hi := twoCoreToCentralizer_component_injective (V.subgroupOf X) (L.subgroupOf X) hr
    (Chapter1.mem_He_iff.mp hX) hcL
  let eB := (MulEquiv.ofBijective (φ.subgroupMap B) ⟨hi,φ.subgroupMap_surjective B⟩).trans
    (MulEquiv.subgroupCongr (twoCoreToCentralizer_image (V.subgroupOf X) (L.subgroupOf X) hr))
  have hB : IsAlternating B 7 := ⟨(eB.trans eL.symm).trans hm.some⟩
  let : B.Normal := EmbeddingSelection.source_larger_A7_image_normal_knownSimple hG K T X hK h3 hTK hAX hX S hS hB
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V.subgroupOf X : Set X)) y
    exact ⟨r x,rfl⟩
  have hn := Subgroup.Normal.map (inferInstance : B.Normal) φ hφ
  rwa [twoCoreToCentralizer_image (V.subgroupOf X) (L.subgroupOf X) hr] at hn
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
