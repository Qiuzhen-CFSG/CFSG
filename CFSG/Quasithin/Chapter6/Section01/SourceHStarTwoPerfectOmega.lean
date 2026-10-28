module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOmegaNormalizer
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup
public import Theory.GroupTheory.TwoPerfectCentralizerCover
public import Theory.GroupTheory.TwoPerfectNormalizerControl
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient

/-!
# Two-perfect subgroup elimination in the H-star orbit centralizer

Put Z = Ω₁(Z(T)), U_L = ⟨Zᴸ⟩ and U_H = ⟨Zᴴ⟩. The natural fixed
quotient and noncentral H-star hypothesis give the precise Thompson cover
J(T) ≤ (T ∩ L) O₂(LT). The two-core centralizes U_L.

A two-perfect Y inside C_H(U_H), with Y = [Y,J(T)], normalizes both T ∩ L
and U_L by the full omega-centralizer argument. The two-group cover
therefore forces Y to centralize U_L. Then [L,Y] ≤ O₂(L), and source
uniqueness over LT gives N_G(Y) ≤ M whenever Y is nontrivial and T-invariant.
If O²(H) also normalizes Y, then H normalizes Y and contradicts H-star
membership. The final theorem proves Y = 1 with these exact source inputs.

The separate existence and normalization of such a Y when C_H(U_H) > O₂(H)
remain with the earlier B.6.8 source producer. This module does not assume
or assert that Y is automatically O²(C_H(U_H)). The natural fixed quotient
also remains the independently produced source 6.1.4 input.

The intentional private imports reuse the left Hall construction and the
checked reduced-module centralizer calculation at their original carriers.
Source: Aschbacher--Smith 6.1.5, printed p.666, second through fifth
paragraphs, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

theorem Input.thompson_le_left_sylow_core_of_natural_quotient
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZ : ¬ Z ≤ (center H).map H.subtype := by
    intro hc
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  rcases hs.borel_thompson_or_five_section
      (hs.thompson_moves_of_noncentral_omega hH hZ) with hJN | hf
  · exact hJN.1
  obtain ⟨A,B,c⟩ := exists_left_cartan_pair h
  have hb := hs.borel_fixes_omega_of_five_section (le_conjugateSpanBy Z L) hf
  have ha : A ≤ centralizer (Z : Set G) := c.left_le.trans hb
  have hfaith := left_cartan_faithful_on_omega c hm
  rw [inf_eq_left.mpr ha] at hfaith
  have hc := c.left_card h.linear h.sylow_normalizes
  rw [hfaith] at hc
  have hpow : 4 ≤ 2^n := by
    calc 4 = 2^2 := by norm_num
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)
  norm_num at hc
  omega

private theorem Input.omega_span_core_centralizes
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let D := L ⊔ (T : Subgroup G)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  have hred := hs.reduced_internal
  rintro x ⟨x',hx',rfl⟩ u hu
  exact congrArg D.subtype
    ((le_centralizer_iff.mp hred.le_centralizer_pCore hx') ⟨u,hs.reduced.1 hu⟩ hu)

private theorem Input.left_omega_span_centralizer_le_core
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    L ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ≤
      L.pCoreIn 2 := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let D := L ⊔ (T : Subgroup G)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  have hc : L ⊓ centralizer (U : Set G) ≤ D.pCoreIn 2 := by
    intro x hx
    have hxD : x ∈ D := (show L ≤ D from le_sup_left) hx.1
    apply mem_map_of_mem D.subtype (x := ⟨x,hxD⟩)
    rw [←hs.reduced_centralizer_core]
    intro u hu
    exact Subtype.ext (hx.2 u hu)
  exact (le_inf inf_le_left hc).trans (inf_pCoreIn_le_of_le 2 le_sup_left)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H Y : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem hstar_twoPerfect_orbit_centralizer_fixes_left_orbit
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hY : IsPPerfect 2 Y)
    (hYC : Y ≤ H ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G))
    (hcomm : Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    Y ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  let hs := h.rankOneInput hout
  have hYomega : Y ≤ H ⊓ centralizer (Z : Set G) :=
    hYC.trans (inf_le_inf_left H (centralizer_le (le_conjugateSpanBy Z H)))
  have hn := hYomega.trans (h.hstar_omega_centralizer_normalizes hH hm hZH)
  apply twoPerfect_centralizes_of_commutator_two_cover Y
    (elementaryAbelianMaxJ (T : Subgroup G)) ((T : Subgroup G) ⊓ L) U hY
    (T.isPGroup'.to_le inf_le_left) (hn.trans inf_le_left) (hn.trans inf_le_right)
    (inf_le_right.trans (le_normalizer_conjugateSpanBy Z L))
    _ hcomm
  exact (hs.thompson_le_left_sylow_core_of_natural_quotient
    (h.maximal_eq_normalizer_L ▸ hH) hm hZH).trans
    (sup_le_sup_left (hs.omega_span_core_centralizes hm) _)

theorem hstar_twoPerfect_orbit_centralizer_normalizer_le_M
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hY : IsPPerfect 2 Y) (hne : Y ≠ ⊥)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hYC : Y ≤ H ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G))
    (hcomm : Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    normalizer (Y : Set G) ≤ M := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  let hs := h.rankOneInput hout
  have hYomega : Y ≤ H ⊓ centralizer (Z : Set G) :=
    hYC.trans (inf_le_inf_left H (centralizer_le (le_conjugateSpanBy Z H)))
  have hYL : Y ≤ normalizer (L : Set G) :=
    h.maximal_eq_normalizer_L ▸ hYomega.trans (hstar_omega_centralizer_le_M hH hZH)
  have hYU := h.hstar_twoPerfect_orbit_centralizer_fixes_left_orbit
    hout hH hm hZH hY hYC hcomm
  have hLC : L ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy Z L).trans (normalizer_le_normalizer_centralizer U)
  have hcommCore : ⁅L,Y⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf (le_normalizer_iff_commutator_le_left.mp hYL) ?_).trans
      (hs.left_omega_span_centralizer_le_core hm)
    exact (commutator_mono le_rfl hYU).trans
      (le_normalizer_iff_commutator_le_right.mp hLC)
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)
  have hQL : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (h.sylow_normalizes_L.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  apply normalizer_le_of_twoPerfect_core_commutator T L H M Y hH.1.1.2 hchar
    (hYC.trans inf_le_left) hTY hY hne hQL hcommCore
  intro N hN hLN
  exact h.maximal_eq_normalizer_L.symm ▸ hs.unique_local_join N hN hLN

/-- A normal two-perfect subgroup of the actual orbit centralizer cannot
be generated by its Thompson commutators. This is the final uniqueness
contradiction for the subgroup Y selected on source p.666. -/
theorem hstar_twoPerfect_orbit_centralizer_eq_bot_of_normalized
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hY : IsPPerfect 2 Y)
    (hHY : H ≤ normalizer (Y : Set G))
    (hYC : Y ≤ H ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G))
    (hcomm : Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆) : Y = ⊥ := by
  by_contra hne
  exact hH.1.2 (hHY.trans
    (h.hstar_twoPerfect_orbit_centralizer_normalizer_le_M hout hH hm hZH hY hne
      (hH.1.1.2.trans hHY) hYC hcomm))

/-- Literal source application: T-invariance and K-normality, where
K=O²(H), supply the normality needed for the uniqueness contradiction. -/
theorem hstar_twoPerfect_orbit_centralizer_eq_bot_of_residual_normalized
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hY : IsPPerfect 2 Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hKY : (pResidual 2 H).map H.subtype ≤ normalizer (Y : Set G))
    (hYC : Y ≤ H ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G))
    (hcomm : Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆) : Y = ⊥ := by
  have hgen : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    have hsyl : (T.subtype hH.1.1.2 : Subgroup H).map H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hH.1.1.2
    simpa only [Subgroup.map_sup,hsyl,←MonoidHom.range_eq_map,range_subtype] using he
  exact h.hstar_twoPerfect_orbit_centralizer_eq_bot_of_normalized hout hH hm hZH hY
    (hgen ▸ sup_le hKY hTY) hYC hcomm

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
