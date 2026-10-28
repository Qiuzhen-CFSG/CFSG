module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeFullSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.ComponentKnownSimple

/-!
# Quasisimplicity of the original larger source quotient

Unique known-simple containment constructs the actual full-span component
and supplies the larger SQTK quotient. The original moved-module argument
then excludes the noncentral-Fitting alternative and yields quasisimplicity
of the literal span quotient. No proper-embedding list is assumed.

Source: Aschbacher–Smith C.5.12–13, printed pp.162–163.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem noncubic_fixedFree_full_span_quotient_quasisimple_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  have hD := EmbeddingSelection.source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  have hquasi : IsQuasisimple E := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
    (EmbeddingSelection.source_larger_quotient_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS) (pCore_quotient_pCore_eq_bot 2) hE heRank
  let f := r.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (r.subgroupMap_surjective _))
  exact IsQuasisimple.of_mulEquiv eD.symm

/-- The actual A₅ source has no noncentral-Fitting containing component.
The central kernel of U(K) is eliminated by its genuine block theorem. -/
theorem alternating_source_full_span_quotient_quasisimple_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  exact noncubic_fixedFree_full_span_quotient_quasisimple_knownSimple hG K T X
    (Or.inr (Or.inr h.block)) h3 (h.module_le.trans inf_le_left) h.twoGroup hTK hAX hX S hS hVC
    h.block.blockFixed_eq_bot
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
