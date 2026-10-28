module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
public import Theory.GroupAction.FixedQuotientExtension
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc

/-!
# From the natural moved-layer quotient to the original omega-span

Let U be the L-span of the original Sylow omega-center. The actual
intersection T ∩ L is Sylow in L, and odd-index averaging gives
U = [U,L] C_U(L). Thus the natural quotient marking on [U,L]/C_[U,L](L)
extends to U/C_U(L), preserving the actor and the coefficient map on the
moved layer. No splitting or trivial fixed kernel is assumed.

The genuine FF alternative supplies either Borel normalization of J(T)
or a symmetric-five section. The latter fixes omega under the Borel,
contradicting faithfulness of the nontrivial original Cartan on its
omega-span. The zero-core common-normal argument therefore makes H
centralize omega even in degree two. Maximal-local uniqueness kills C_U(L),
so the extended quotient map gives a full natural model. The checked
natural degree bound then yields n = 2 or 4 and small Cartan generation.

This discharges the moved-layer-to-whole-span transfer and the degree-two
centralization in the natural row. Exhaustive source model selection and
the remaining prime-pair recognition branches remain with final assembly.
The two `import all` lines deliberately continue the existing internal
Cartan/common-normal proof, without changing its public boundaries.

Source: Aschbacher--Smith B.2.14, 5.1.2, 5.1.3(3), 5.1.6(2), and 5.2.2,
printed pp.78,630--632,647 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

/-- The same natural quotient extends across a fixed supplement. -/
theorem IsNaturalFixedQuotient.of_fixed_supplement
    {L U V : Subgroup G} {n : ℕ} [IsMulCommutative U]
    (hm : IsNaturalFixedQuotient L V n) (hVU : V ≤ U)
    (hn : L ≤ normalizer (U : Set G))
    (hs : U = V ⊔ (U ⊓ centralizer (L : Set G))) :
    IsNaturalFixedQuotient L U n := by
  obtain ⟨F,_,_,_,hF,e,m,he⟩ := hm
  let := ZMod.algebra F 2
  obtain ⟨m',hactor,_⟩ := m.exists_extension_of_fixed_supplement hVU hn hs
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,e,m',hactor.trans he⟩

namespace RankOneGeneric
variable [Finite G]

/-- Sylow averaging supplies the actual central supplement of the original omega-span. -/
theorem Input.omega_span_eq_layer_sup_fixed
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    U = layer L U ⊔ (U ⊓ centralizer (L : Set G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let := hu.1
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  apply conjugateSpan_split_of_sylow_fixed P
  intro z hz a ha
  obtain ⟨a,ha,rfl⟩ := ha
  have haT : (a : G) ∈ (T : Subgroup G) := by
    rw [hP] at ha
    exact ha
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 a haT

/-- Source 5.1.3(3) on the moved omega-span yields the whole fixed quotient.
The supplement is proved from the actual Sylow placement, not assumed. -/
theorem Input.omega_span_natural_quotient_of_layer
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsNaturalFixedQuotient L
      (layer L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) n) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let := hu.1
  exact hm.of_fixed_supplement
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z L))
    (le_normalizer_conjugateSpanBy Z L) h.omega_span_eq_layer_sup_fixed

private theorem natural_quotient_borel_thompson_of_noncentral_omega
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  rcases hs.borel_thompson_or_five_section
      (hs.thompson_moves_of_noncentral_omega hH hZ) with hJN | hf
  · exact hJN.2
  have hb := hs.borel_fixes_omega_of_five_section (le_conjugateSpanBy Z L) hf
  have ha : A ≤ centralizer (Z : Set G) := c.left_le.trans hb
  have he : conjugateSpanBy Z A = Z := le_antisymm
    (conjugateSpanBy_le le_rfl (ha.trans (Subgroup.centralizer_le_normalizer _)))
    (le_conjugateSpanBy Z A)
  have hfaith := (h.natural_quotient_cartan_span c hm).2.1
  rw [he,inf_eq_left.mpr ha] at hfaith
  have hc := c.left_card h.linear h.sylow_normalizes
  rw [hfaith] at hc
  have hpow : 4 ≤ 2^n := by
    calc 4 = 2^2 := by norm_num
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)
  norm_num at hc
  omega

/-- In the natural quotient branch H centralizes omega even at degree two.
The actual symmetric-five alternative fixes omega under the left Borel,
contradicting the faithful original Cartan action. -/
theorem Input.natural_quotient_cartan_omega_centralizes_all_degrees
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) : H ≤ omegaCentralizer T := by
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hZ
    have hJN := natural_quotient_borel_thompson_of_noncentral_omega h hH c hm hZ
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    let J := A ⊔ (T : Subgroup G)
    let hq := h.natural_quotient_cartan_qrc_hypotheses hH c hm hz
    let d := natural_quotient_cartan_qrc_configuration h hH c hm hz
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hE => hE.1
    have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ J.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right)
        ((sup_le_sup_right c.left_le _).trans hJN)
    have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (X : Set G) :=
      hJcore.trans (hq.core_eq_centralizer ▸ inf_le_right)
    let S := T.subtype (show (T : Subgroup G) ≤ H from hH.1.1.2)
    let Z := omegaOneCenterAmbient (S : Subgroup H)
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    have hU : IsPReduced 2 U := hq.sylowOmega_reduced (h.qtke.evenCharacteristic T)
    let := hU.normal
    have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
      fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    have hzmap : Z.map H.subtype = omegaOneCenterAmbient (T : Subgroup G) := by
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hZU : Z ≤ U := by
      intro z hz
      apply le_conjugateSpanBy
      exact hzmap ▸ mem_map_of_mem H.subtype hz
    have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hJn : ¬ (elementaryAbelianMaxJ (S : Subgroup H)).Normal := by
      intro hnormal
      let := hnormal
      have hnorm := (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hjmap] at hnorm
      obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_thompson_normal h.maximal hJ hnorm
      exact hN (d.no_common_normal N hNR (by
        simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
    have hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤ := by
      obtain ⟨K,⟨hK,hTK⟩,hk⟩ := Chapter3.HStar.unique_maximal_subgroup T h.sylow_normalizes hH
      have hSK : (S : Subgroup H) ≤ K := by
        intro t ht
        obtain ⟨k,hk,he⟩ := hTK ht
        exact H.subtype_injective he ▸ hk
      refine ⟨hSK.trans_lt hK.lt_top,K,⟨hSK,hK.covBy_top⟩,?_⟩
      intro C hC
      apply hk C
      exact ⟨hC.2.isCoatom,fun t ht => ⟨⟨t,hH.1.1.2 ht⟩,hC.1 ht,rfl⟩⟩
    have hj := thompson_not_centralizes_of_unique_maximal S U Z hZU
      (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
      (fun hc => hZ (by rw [←hzmap]; exact map_mono hc)) hu hJn
    have hRne : J.pCoreIn 2 ≠ ⊥ := by
      intro he
      have hX : X = ⊥ := bot_unique (d.module_le_core.trans_eq he)
      exact (h.natural_quotient_cartan_span c hm).2.2 hX
    have hp := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
    obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_residual_sylow
      (Chapter3.source_common_normal_knownSimple h.qtke T) hRne
      (residual_sylow_of_reduced_module hq h.qtke hp hJ U hU hj)
    exact hN (d.no_common_normal N hNR (by
      simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
  intro x hx z hz'
  obtain ⟨a,ha,rfl⟩ := hZ hz'
  exact (congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)).symm


/-- The moved-layer quotient supplies a full natural omega-span model in
all degrees. Both outside centralization and the fixed-kernel removal are
proved here, including the degree-two case. -/
theorem Input.natural_layer_quotient_cartan_model
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (layer L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    H ≤ omegaCentralizer T ∧ U ⊓ centralizer (L : Set G) = ⊥ ∧
      IsNaturalModule L U n := by
  have hwhole := h.omega_span_natural_quotient_of_layer hm
  have hHC := h.natural_quotient_cartan_omega_centralizes_all_degrees hH hgen c hwhole hz
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hwhole (le_centralizer_iff.mp hc)
  have hf := (h.omega_span_input hLC).reduced_fixed_eq_bot_of_outside_centralizes hH hHC
  exact ⟨hHC,hf,hwhole.natural_of_fixed_eq_bot hf⟩

/-- The genuine moved-layer natural quotient gives degree two or four and
small generation for the original Cartans. -/
theorem Input.natural_layer_quotient_cartan_degree_and_smallGeneration
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (layer L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n :=
  h.natural_quotient_cartan_degree_and_smallGeneration hH hgen c
    (h.omega_span_natural_quotient_of_layer hm) hz

end RankOneGeneric
end CFSG.Quasithin.Chapter6.Source
