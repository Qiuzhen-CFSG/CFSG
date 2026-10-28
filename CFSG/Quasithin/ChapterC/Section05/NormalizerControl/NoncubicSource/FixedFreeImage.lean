module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.FixedFreeAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalComponent
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FullSpanKernel
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.AlternatingSeven

/-!
# The exact larger-group action kernel for the A₇ source blocks

The original reduced span V contains U(L). Both A₇ block types have
trivial fixed layer, so the three-subgroups argument makes O₂(L)
centralize V. The actual centralizer quotient thus has kernel O₂(L)
on L. Characteristic two compares this image with L's literal image in
X/O₂(X), and the proved A.3.12 row sieve makes that image normal.
This discharges the former larger-quotient model premise for every
proper A₇ enlargement in C.5.13.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163.
-/
public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02.LocalModels
variable {G : Type*} [Group G]

theorem short_fixedFree_centralizer_image_equiv
    (L X V : Subgroup G) (hL : IsShort L)
    (hLX : L ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U L ≤ V) [IsElementaryAbelian 2 V]
    (hVL : ⁅V,L⁆ ≤ U L) (hz : blockFixed L = ⊥) :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    Nonempty ((L ⧸ pCore 2 L) ≃*
      (L.subgroupOf X).map (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)))) := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let E := (subgroupOfEquivOfLe hLX).symm
  let f := (q.subgroupMap (L.subgroupOf X)).comp E.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp E.surjective
  have hcore := hL.core_centralizes_of_fixedFree_moved hVL hUV hz
  have hk : f.ker = pCore 2 L := by
    apply le_antisymm
    · intro l hl
      rw [←hL.centralizer_blockU]
      intro u hu
      apply Subtype.ext
      have he : q (E l : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
      have hc := (QuotientGroup.eq_one_iff _).mp he
      exact congrArg X.subtype (hc ⟨u,hVX (hUV (mem_map_of_mem L.subtype hu))⟩
        (hUV (mem_map_of_mem L.subtype hu)))
    · intro l hl
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff _).mpr
      intro v hv
      exact Subtype.ext (hcore (mem_map_of_mem L.subtype hl) v hv)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

universe u
theorem noncubic_a7_source_image_normal {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
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
  have hlocal := EmbeddingSelection.source_larger_local_family hG hA312 K T X hK h3 hTK hAX hX S hS
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
  let : B.Normal := EmbeddingSelection.source_larger_A7_image_normal hG hA312 K T X hK h3 hTK hAX hX S hS hB
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V.subgroupOf X : Set X)) y
    exact ⟨r x,rfl⟩
  have hn := Subgroup.Normal.map (inferInstance : B.Normal) φ hφ
  rwa [twoCoreToCentralizer_image (V.subgroupOf X) (L.subgroupOf X) hr] at hn
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
