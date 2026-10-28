module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOvergroupAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalLayer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalLayer
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc

/-!
# The natural-quotient Cartan overgroup in source 6.1.5

For a noncentral H-star member, the natural quotient on the original L-span
of the Sylow omega-center makes the Cartan join have nontrivial two-core.
The proof uses the source 3.1.7 common-normal theorem and E.2.3 on the
literal H-star omega orbit. The proved Baumann normalizer bound supplies
minimal parabolicity, so no generation-parameter-greater-than-one premise
is needed. This is the specialization of 5.1.7(2)(iii) used by 6.1.5.

The final theorem applies the existing B.5.6 classification to this precise
join. The compatible Hall pair and natural-quotient marking remain earlier
source inputs; the full centralizer and F.1.12 endgame are separate steps.
The three `import all` lines continue the existing private Cartan argument
without changing its public declarations.

Source: Aschbacher--Smith 3.1.7, 5.1.6--7 and 6.1.5, printed pp.575--576,
632--634 and 666--667.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The natural Cartan join has nontrivial two-core even when n(H) = 1. -/
theorem Input.hstar_cartan_join_core_ne_bot_of_natural_quotient
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    (A ⊔ H).pCoreIn 2 ≠ ⊥ := by
  intro hz
  have hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro hc
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
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
  have hRne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hX : X = ⊥ := bot_unique (d.module_le_core.trans_eq he)
    exact (h.natural_quotient_cartan_span c hm).2.2 hX
  obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_residual_sylow
    (Chapter3.source_common_normal_knownSimple h.qtke T) hRne
    (residual_sylow_of_reduced_module hq h.qtke (h.hstar_minimal_parabolic hH) hJ _
      (h.hstar_omega_orbit_reduced hH) (h.hstar_thompson_moves_omega_orbit hH hZH))
  exact hN (d.no_common_normal N hNR (by
    simpa only [Chapter3.generated_eq_sup] using
      (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H A B : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The original 6.1.5 Cartan join belongs to H(T), with no membership premise. -/
theorem hstar_cartan_join_mem_HOver
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (c : RankOneGeneric.CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    A ⊔ H ∈ Chapter1.HOver G (T : Set G) := by
  exact ⟨(h.rankOneInput hout).hstar_cartan_join_core_ne_bot_of_natural_quotient
    (h.maximal_eq_normalizer_L ▸ hH) c hm hZH,
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right⟩

/-- The literal B.5.6 consumer with membership of the Cartan join discharged. -/
theorem hstar_cartan_offender_classification
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (c : RankOneGeneric.CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let X := A ⊔ H
    let hX := h.hstar_cartan_join_mem_HOver hout hH c hm hZH
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI : U.Normal := (h.overgroup_omega_orbit_reduced hX).normal
    letI : IsElementaryAbelian 2 U := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ : Representation (ZMod 2) (X ⧸ C) (Additive U) :=
      NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    Representation.BinaryOffender.IsFFModule ρ ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative
        (ρ.comp (Representation.BinaryOffender.offenderSubgroup ρ).subtype) := by
  exact h.hstar_overgroup_offender_classification hout hH hZH le_sup_right
    (h.hstar_cartan_join_mem_HOver hout hH c hm hZH)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
