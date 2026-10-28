module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeFullSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingTransport
/-!
# The actual fixed-free C.5.12 larger-component row selection

When the auxiliary span equals K, its original fixed-free block identifies
the smaller image in X/O₂(X) with K/O₂(K). The literal A.3.12 embedding,
rank-two residual theorem and independently proved J₄ exclusion select
the five remaining models. Each model is transported to the intrinsic
quotient of the full conjugate span through its exact two-core kernel.
The theorem retains the genuine universal A.3.12 source input.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

theorem fixedFree_full_span_selection
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hz : blockFixed K = ⊥)
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K)
    (hJ4 : let D := conjugateSpanBy K X
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
  have hlocal := (source_larger_local_family hG hA312 K T X hK h3 hTK hAX hX S hS).1
  rw [hLK] at hlocal
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : K.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp hlocal
  have hBmem : B ∈ ChapterA.Section03.localCComponents Q :=
    mem_L_map_twoCore_mem_localCComponents hmem
  obtain ⟨hD,hrows⟩ := source_larger_span_embedding hG hA312 K T X hK h3 hTK hAX hX S hS
  rw [hLK] at hrows
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
  have hJ4E : ¬ Nonempty (E ≃* Janko4.Model) := by
    rintro ⟨e⟩
    exact hJ4 ⟨eD.trans e⟩
  obtain ⟨n,hn,hm⟩ := noncubic_binary_model K hK h3
  have hout := select_binary_rows_without_faithfulness B E hn (hm.of_mulEquiv eK.symm)
    hBE hJ4E hrows (fun hm hr => eq_of_rankTwo_parabolic_model Q hBmem hE hBE hm hr)
  rcases hout with he | ⟨_,hmodels⟩
  · exact .inl he
  · exact .inr (surviving_models_transport eD.symm hmodels)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
