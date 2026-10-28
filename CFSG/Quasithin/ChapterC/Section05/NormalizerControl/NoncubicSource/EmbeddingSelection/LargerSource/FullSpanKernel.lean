module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FittingPairSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.Embedding
public import Theory.GroupTheory.CharacteristicTwoCommutatorKernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
/-!
# The full source span and its exact component kernel

The original reduced source gives [O₂(X),K]=U(K). Passing to the normal
closure D=⟨K^X⟩ yields [O₂(X),D]=V=[V,D]=U(D) for V=⟨U(K)^X⟩.
Characteristic two then identifies the action kernel on D with O₂(D)
and makes the canonical two-core-to-centralizer quotient map injective
on its image. The genuine A.3.12 application identifies this normal
closure with the containing component, preserving both literal quotients.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem source_normal_span_core (K V : Subgroup G) (hK : IsShort K)
    (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hV : IsPReduced 2 V) (hgen : V = conjugateSpanBy (U K) ⊤) :
    let D := conjugateSpanBy K ⊤
    ⁅pCore 2 G,D⁆ = V ∧ ⁅V,D⁆ = V ∧ U D = V := by
  let D := conjugateSpanBy K ⊤
  let : D.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (le_normalizer_conjugateSpanBy K ⊤))
  let : V.Normal := hV.normal
  have hUV : U K ≤ V := hgen ▸ le_conjugateSpanBy (U K) ⊤
  have hKD : K ≤ D := le_conjugateSpanBy K ⊤
  have hQK := source_core_commutator_of_reduced K V hK S hSK hV hUV
  have hQD : ⁅pCore 2 G,D⁆ ≤ V := by
    let W := commutatorPreimage ⊤ (pCore 2 G) V
    have hKW : K ≤ W := le_commutatorPreimage le_top (by rwa [commutator_comm,hQK])
    have hNW : (⊤ : Subgroup G) ≤ normalizer (W : Set G) :=
      commutatorPreimage_normalized _ _ _ _ le_normalizer_of_normal
        le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
    have hDW : D ≤ W := conjugateSpanBy_le hKW hNW
    rw [commutator_comm]
    exact (commutator_mono hDW le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  have hQDeq : ⁅pCore 2 G,D⁆ = V := by
    apply le_antisymm hQD
    rw [hgen]
    exact conjugateSpanBy_le (hQK.symm.le.trans (commutator_mono le_rfl hKD))
      le_normalizer_of_normal
  have hUK : ⁅U K,K⁆ = U K := by
    have hi := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
      hK.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    simpa only [U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  have hVD : ⁅V,D⁆ = V := by
    apply le_antisymm (commutator_le_left _ _)
    calc
      V = conjugateSpanBy (U K) ⊤ := hgen
      _ ≤ ⁅V,D⁆ := conjugateSpanBy_le (hUK.symm.le.trans (commutator_mono hUV hKD))
        le_normalizer_of_normal
  have hVDle : V ≤ D := by
    rw [hgen]
    exact conjugateSpanBy_le ((map_subtype_le _).trans hKD) le_normalizer_of_normal
  have hVDcore : V ≤ D.pCoreIn 2 := le_pCoreIn_of_normalizes
    hV.elementary.isPGroup hVDle le_normalizer_of_normal
  have hDQ : D.pCoreIn 2 ≤ pCore 2 G := by
    change (pCore 2 D).map D.subtype ≤ pCore 2 G
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map D.subtype⟩
  have he : ⁅D.pCoreIn 2,D⁆ = V := le_antisymm
    ((commutator_mono hDQ le_rfl).trans hQD)
    (hVD.symm.le.trans (commutator_mono hVDcore le_rfl))
  refine ⟨hQDeq,hVD,?_⟩
  rw [← he]
  change (⁅pCore 2 D,(⊤ : Subgroup D)⁆).map D.subtype = _
  rw [map_commutator,← MonoidHom.range_eq_map,range_subtype]
  rfl
omit [Finite G] in
private theorem source_u_subgroupOf (K X : Subgroup G) (hKX : K ≤ X) :
    U (K.subgroupOf X) = (U K).subgroupOf X := by
  let e := subgroupOfEquivOfLe hKX
  have he : (blockU (K.subgroupOf X)).map e.toMonoidHom = blockU K := by
    rw [blockU,map_commutator,pCore_map_iso,← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  apply map_injective X.subtype_injective
  rw [map_subgroupOf_eq_of_le hUX]
  change ((blockU (K.subgroupOf X)).map (K.subgroupOf X).subtype).map X.subtype = _
  rw [map_map]
  change (blockU (K.subgroupOf X)).map (K.subtype.comp e.toMonoidHom) = _
  rw [← map_map,he]
  rfl

theorem noncubic_full_span_kernel
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hKX : K ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let V := conjugateSpanBy (U K) X
    let D := conjugateSpanBy K X
    let hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
    let : (V.subgroupOf X).Normal := hr.normal
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    ⁅pCore 2 X,D.subgroupOf X⁆ = V.subgroupOf X ∧
      U (D.subgroupOf X) = V.subgroupOf X ∧
      (q.subgroupMap (D.subgroupOf X)).ker = pCore 2 (D.subgroupOf X) ∧
      Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃*
        (D.subgroupOf X).map q) ∧
      Function.Injective ((twoCoreToCentralizer (V.subgroupOf X) hr).subgroupMap
        ((D.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))) := by
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hDX : D ≤ X := conjugateSpanBy_le_self hKX
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hr.normal
  let : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (le_normalizer_conjugateSpanBy K X)
  have hSK : (S : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hKX]
    intro s hs
    exact hTK (hS ▸ mem_map_of_mem X.subtype hs)
  have hshort : IsShort (K.subgroupOf X) :=
    hK.chi.short.of_mulEquiv (subgroupOfEquivOfLe hKX).symm
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  have hVspan : V.subgroupOf X = conjugateSpanBy (U (K.subgroupOf X)) ⊤ := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hVX,map_conjugateSpanBy,source_u_subgroupOf K X hKX,
      map_subgroupOf_eq_of_le hUX,← MonoidHom.range_eq_map,range_subtype]
  have hDspan : conjugateSpanBy (K.subgroupOf X) ⊤ = D.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKX,← MonoidHom.range_eq_map,
      range_subtype,map_subgroupOf_eq_of_le hDX]
  have hc := source_normal_span_core (K.subgroupOf X) (V.subgroupOf X) hshort S hSK hr hVspan
  rw [hDspan] at hc
  have hchar := Chapter1.mem_He_iff.mp hX
  exact ⟨hc.1,hc.2.2,reduced_component_action_kernel _ _ hr hchar hc.1.le,
    reduced_component_action_equiv _ _ hr hchar hc.1.le,
    twoCoreToCentralizer_component_injective _ _ hr hchar hc.1.le⟩

namespace EmbeddingSelection
open Chapter1.Section02
universe u
theorem source_larger_span_embedding {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    let D := conjugateSpanBy K X
    (D.subgroupOf X).IsCComponent ∧
      A312Embedding ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
        ((D.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let D := conjugateSpanBy K X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hDX : D ≤ X := conjugateSpanBy_le_self hKX
  obtain ⟨E,hE,hLE,_hu,hEn,hemb⟩ := source_larger_embedding hG hA312 K T X hK h3 hTK hAX hX S hS
  let : E.Normal := hEn
  have hKE : K.subgroupOf X ≤ E := (subgroupOf_mono X (le_conjugateSpanBy K N)).trans hLE
  have hnsolv : ¬ Group.IsSolvable (K.subgroupOf X) := by
    intro hs
    let : Group.IsSolvable (K.subgroupOf X) := hs
    have hh : Group.IsSolvable K := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hKX).toMonoidHom) (subgroupOfEquivOfLe hKX).surjective
    exact Chapter1.mem_L_not_isSolvable
      (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS).1.2 hh
  have hspan := normal_span_eq_component (K.subgroupOf X) E hE hKE hnsolv
  have hEq : D.subgroupOf X = E := by
    apply map_injective X.subtype_injective
    rw [← hspan,map_conjugateSpanBy,map_subgroupOf_eq_of_le hKX,
      ← MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hDX]
  change (D.subgroupOf X).IsCComponent ∧ A312Embedding
    ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
    ((D.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
  rw [hEq]
  exact ⟨hE,hemb⟩
end EmbeddingSelection
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
