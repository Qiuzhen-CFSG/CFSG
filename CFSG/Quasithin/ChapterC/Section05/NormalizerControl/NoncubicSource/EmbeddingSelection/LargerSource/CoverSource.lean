module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeTwoCoreImage
public import Theory.GroupTheory.PCoreSurjective
/-!
# The actual noncubic block image, including its central cover

The original reduced module makes the block image quasisimple in the
two-core quotient. Its further two-core quotient is the original binary
PSL2 model. The defining-prime cover theorem therefore leaves precisely
the binary simple image or SL2(5) at exponent two. In particular no
fixed-free hypothesis on the original block module is introduced.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
theorem noncubic_twoCore_small_models_with_quotient
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let B := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    IsQuasisimple B ∧ ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∧
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n) ∧
      (ClassicalGroup.IsPSL B 2 (2^n) ∨ n = 2 ∧ IsSL B 2 5) := by
  let V := conjugateSpanBy (U K) X
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  have hVX : V ≤ X := conjugateSpanBy_le_self hUX
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let r := QuotientGroup.mk' (pCore 2 X)
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let B := (K.subgroupOf X).map r
  let E := (K.subgroupOf X).map q
  let : IsQuasisimple E := short_centralizer_image_quasisimple K X V hK.chi.short hKX hVX hXV
    (le_conjugateSpanBy _ _)
  let φ := twoCoreToCentralizer (V.subgroupOf X) hr
  have hcK : ⁅pCore 2 X,K.subgroupOf X⁆ ≤ V.subgroupOf X :=
    (commutator_mono le_rfl (subgroupOf_mono X (le_conjugateSpanBy K X))).trans
      (noncubic_full_span_kernel K T X hK h3 hUT hT hTK hKX hX S hS hVC).1.le
  have hi := twoCoreToCentralizer_component_injective (V.subgroupOf X) (K.subgroupOf X) hr
    (Chapter1.mem_He_iff.mp hX) hcK
  let eB := (MulEquiv.ofBijective (φ.subgroupMap B) ⟨hi,φ.subgroupMap_surjective B⟩).trans
    (MulEquiv.subgroupCongr (twoCoreToCentralizer_image (V.subgroupOf X) (K.subgroupOf X) hr))
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB.symm
  let eK := (subgroupOfEquivOfLe hKX).symm
  let f := (r.subgroupMap (K.subgroupOf X)).comp eK.toMonoidHom
  have hf : Function.Surjective f := (r.subgroupMap_surjective _).comp eK.surjective
  have hf2 : IsPGroup 2 f.ker := by
    let i : f.ker →* pCore 2 X :=
      ((inclusion hKX).comp f.ker.subtype).codRestrict _ (by
        intro k
        apply (QuotientGroup.eq_one_iff _).mp
        exact congrArg Subtype.val k.property)
    exact (pCore_isPGroup (p := 2) (G := X)).of_injective i (by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : pCore 2 X => (z.val : G)) he)
  let g := (QuotientGroup.mk' (pCore 2 B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgk : g.ker = pCore 2 K := by
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hf2
  let e := (QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)
  obtain ⟨n,hn,hm⟩ := noncubic_binary_model K hK h3
  exact ⟨inferInstance,n,hn,hm,hm.of_mulEquiv e.symm,quasisimple_binary_core_models hn (hm.of_mulEquiv e.symm)⟩
theorem noncubic_twoCore_small_models
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let B := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    IsQuasisimple B ∧ ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∧
      (ClassicalGroup.IsPSL B 2 (2^n) ∨ n = 2 ∧ IsSL B 2 5) := by
  obtain ⟨hB,n,hn,hm,_,hmodels⟩ := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  exact ⟨hB,n,hn,hm,hmodels⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
