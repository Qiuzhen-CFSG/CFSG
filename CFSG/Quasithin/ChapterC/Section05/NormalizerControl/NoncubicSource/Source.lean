module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Natural
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Alternating
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.QuotientAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceEmbedding
/-!
# The genuine noncubic preliminaries of C.5.13

Both original noncubic block alternatives supply their noncentral full-Sylow
fixed seed. Thus the literal auxiliary omega-center span contains all of U,
is elementary and two-reduced, has Sylow centralizer P₁, and satisfies [V₁,K]=U.
Its original Sylow image normalizes and acts faithfully on the block image.
The preceding embedding theorem applies the universal earlier A.3.12/A.3.8
theorems to the actual conjugate span, with local SQTK inherited from QTKE.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- Both genuine noncubic block types supply the full-T fixed seed. -/
theorem noncubic_noncentral_fixed (K T : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G)) :
    ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G) := by
  rcases hK with ⟨n,hn⟩ | ha | ha
  · exact natural_noncentral_fixed hn hT hUT hTK
  · exact (h3 ha).elim
  · exact alternating_five_noncentral_fixed K T ha hT hUT hTK
/-- All span, reducedness, core-centralizer and moved-module assertions,
with the I.2.3 premise discharged on the original module. -/
theorem noncubic_source_span (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    IsElementaryAbelian 2 V ∧ V ≤ N ∧ N ≤ normalizer (V : Set G) ∧
      U K ≤ V ∧ V ≤ T ∧ T ⊓ centralizer (V : Set G) = (K ⊔ T).pCoreIn 2 ∧
      Theory.GroupTheory.IsPReduced 2 (V.subgroupOf N) ∧ ⁅V,K⁆ = U K := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  obtain ⟨he,hVN,hNV,hUV,hVT,hCV⟩ := source_omega_span_of_noncentral_fixed K T X
    hK.chi.short hT hTK P hP hA hAX (noncubic_noncentral_fixed K T hK h3 hT hUT hTK)
  refine ⟨he,hVN,hNV,hUV,hVT,hCV,source_omega_span_reduced K T X P hP hA hAX S hS,?_⟩
  let : IsElementaryAbelian 2 V := he
  have hVC : V ≤ centralizer (U K : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
  have hUK : ⁅U K,K⁆ = U K := by
    have hi := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
      hK.chi.short.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    simpa only [U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  apply le_antisymm
  · rw [commutator_comm]
    exact block_fixer_displacement hK.chi.short (hVT.trans hTK) hVC
  · exact hUK.symm.trans_le (commutator_mono hUV le_rfl)
/-- The exact full Sylow action on X₁/C_X₁(V₁), with no fixed-point,
quotient-order, or faithful-action premise. -/
theorem noncubic_source_quotient_action (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    (∃ B : Sylow 2 (N ⧸ centralizer (V.subgroupOf N : Set N)),
      (B : Subgroup _) = (T.subgroupOf N).map q) ∧
    (T.subgroupOf N).map q ≤ normalizer ((K.subgroupOf N).map q : Set _) ∧
    (T.subgroupOf N).map q ⊓ centralizer ((K.subgroupOf N).map q : Set _) = ⊥ ∧
    Nonempty ((K ⧸ pCore 2 K) ≃* (K.subgroupOf N).map q) := by
  have hf := noncubic_noncentral_fixed K T hK h3 hT hUT hTK
  have ha := source_omega_quotient_sylow_action K T X hK h3 hT hTK P hP hA hAX S hS hf
  exact ⟨ha.1,ha.2.1,ha.2.2,
    source_omega_block_quotient K T X hK.chi.short hT hTK P hP hA hAX hf⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
