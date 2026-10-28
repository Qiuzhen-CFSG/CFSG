module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeTwoCoreImage
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
/-!
# Quasisimplicity of the full A₅ source span

A fixed-free original block has its exact binary PSL₂ image in X/O₂(X).
Its two-rank is at least two, so the containing C-component cannot have
noncentral Fitting subgroup by the completed A.3.6 rank-one calculation.
The intrinsic two-core quotient is then quasisimple. The A₅ source wrapper
removes the fixed-layer premise by the genuine block theorem. The natural
case with a nonzero fixed layer remains separate.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem noncubic_fixedFree_full_span_quotient_quasisimple
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hUT : U K ≤ T) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hz : blockFixed K = ⊥) :
    let D := conjugateSpanBy K X
    IsQuasisimple ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) := by
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
    let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
    exact conjugateSpanBy_elementary_of_commutative (U K) X
  obtain ⟨eK⟩ := short_fixedFree_twoCore_image_equiv K X V hK.chi.short hKX hVX hXV
    (le_conjugateSpanBy _ _) S (hS ▸ hTK) hr (Chapter1.mem_He_iff.mp hX) hz
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let E := (D.subgroupOf X).map r
  obtain ⟨n,hn,hm⟩ := EmbeddingSelection.noncubic_binary_model K hK h3
  have hb : n ≤ primeRank 2 B := EmbeddingSelection.binary_rank_lower (hm.of_mulEquiv eK.symm)
  have hBE : B ≤ E := map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))
  have heRank : 2 ≤ primeRank 2 E := (by omega : 2 ≤ n).trans (hb.trans (primeRank_mono 2 hBE))
  have hXH : X ∈ Chapter1.H G := by
    intro he
    have hU : U K = ⊥ := by
      apply bot_unique
      intro v hv
      have hcore : (⟨v,hVX ((le_conjugateSpanBy _ _) hv)⟩ : X) ∈ pCore 2 X :=
        hr.le_pCore ((le_conjugateSpanBy _ _) hv)
      exact he ▸ mem_map_of_mem X.subtype hcore
    exact hK.chi.short.blockU_ne_bot ((map_eq_bot_iff_of_injective (blockU K) K.subtype_injective).mp hU)
  have hD := (EmbeddingSelection.source_larger_span_embedding hG hA312 K T X hK h3 hTK hAX hX S hS).1
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  have hquasi : IsQuasisimple E := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
    (uniqueness_local_quotient_sqtk hG hXH) (pCore_quotient_pCore_eq_bot 2) hE heRank
  let f := r.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (r.subgroupMap_surjective _))
  exact IsQuasisimple.of_mulEquiv eD.symm

/-- The actual A₅ source has no noncentral-Fitting containing component.
The central kernel of U(K) is eliminated by its genuine block theorem. -/
theorem alternating_source_full_span_quotient_quasisimple
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let D := conjugateSpanBy K X
    IsQuasisimple ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) := by
  have h3 : ¬ IsAlternatingBlock K 3 := by
    intro hthree
    obtain ⟨e5⟩ := h.block.2.2.quotient_iso
    obtain ⟨e3⟩ := hthree.2.2.quotient_iso
    have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
    have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card,card_alternatingGroup]
      decide
    have hthreecard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card,card_alternatingGroup]
      decide
    rw [h5,hthreecard] at hc
    omega
  exact noncubic_fixedFree_full_span_quotient_quasisimple hG hA312 K T X
    (Or.inr (Or.inr h.block)) h3 (h.module_le.trans inf_le_left) h.twoGroup hTK hAX hX S hS hVC
    h.block.blockFixed_eq_bot
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
