module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FixedFreeRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryKnownSimple
/-!
# The original fixed-free larger-span selector without A.3.12 premises

The fixed-free source identifies the smaller quotient image with its binary
block model. The known-simple local-family and span-component producers put
that image inside its actual containing component. The complete restricted
binary selector gives equality or one of the five source models; the exact
two-core kernel transports them to the intrinsic full-span quotient.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem fixedFree_full_span_selection_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hz : blockFixed K = ⊥)
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K)
    (_hJ4 : let D := conjugateSpanBy K X
      ¬ Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko4.Model)) :
    let D := conjugateSpanBy K X
    let r := QuotientGroup.mk' (pCore 2 X)
    (K.subgroupOf X).map r = (D.subgroupOf X).map r ∨
      IsAlternating ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
      IsAlternatingCover ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
      Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 25 ∨
      ∃ p, A312ExceptionalPrime p ∧
        ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 p := by
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
    let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
    exact conjugateSpanBy_elementary_of_commutative (U K) X
  obtain ⟨eK⟩ := short_fixedFree_twoCore_image_equiv K X V hK.chi.short hKX hVX hXV
    (le_conjugateSpanBy _ _) S (hS ▸ hTK) hr (Chapter1.mem_He_iff.mp hX) hz
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let E := (D.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal := (source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS).1
  rw [hLK] at hlocal
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : K.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp hlocal
  have hBmem : B ∈ ChapterA.Section03.localCComponents Q :=
    mem_L_map_twoCore_mem_localCComponents hmem
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  have hBE : B ≤ E := map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eK
  let f := r.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (r.subgroupMap_surjective _))
  have hsetup := source_larger_restricted_setup_knownSimple hG K T X hK h3 hTK hAX hX S hS hLK
  have hSQTK := source_larger_quotient_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨n,hn,hm⟩ := noncubic_binary_model K hK h3
  rcases binary_larger_selection_knownSimple hSQTK (pCore_quotient_pCore_eq_bot 2 (G := X))
    Q hBmem hE hBE hsetup.2.2.2 hn (hm.of_mulEquiv eK.symm) with he | ⟨_,hmodels⟩
  · exact .inl he
  · exact .inr (surviving_models_transport eD.symm hmodels)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
