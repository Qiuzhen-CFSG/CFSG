module


public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceBound
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.NoncentralMovement
public import CFSG.Quasithin.ChapterB.Section06To07.NormalActor
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization
public import CFSG.Quasithin.Chapter6.Section01.SourceCentralLine
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# E.2.3 input from the literal Chapter 6.1 H-star omega orbit

This extension packages the rank-one H-star localization and feeds the
original reduced omega orbit into the unconditional E.2.3 source alternative.
It retains the exact centralizer quotient and makes no natural-module
assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher CFSG.Quasithin.ChapterB Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}

namespace RankOneGeneric.Input

theorem hstar_minimal_parabolic
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hp := Chapter3.HStar.minimalParabolic T h.sylow_normalizes hH
    (Or.inl ((normalizer_le_normalizer_baumann (T : Subgroup G)).trans
      h.baumann_normalizer_le))
  exact ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T H hp

theorem hstar_omega_orbit_reduced
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (S : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hTH)]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1)
  have hr := omegaCenter_normalClosure_reduced S hc
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hTH)] at hr
  exact hr

omit [Finite G] in
theorem hstar_omega_orbit_centralizer_proper
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    centralizer (((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) ≠ ⊤ := by
  intro he
  apply hZH
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz x hx
  have hzH : z ∈ H := hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hc : (⟨x, hx⟩ : H) ∈ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) :=
    he.symm ▸ mem_top _
  exact (congrArg H.subtype (hc ⟨z, hzH⟩ (le_conjugateSpanBy _ _ hz))).symm

theorem hstar_baumann_not_normal
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ (ChapterB.baumann (T.subtype hH.1.1.2 : Subgroup H)).Normal := by
  let S := T.subtype hH.1.1.2
  intro hB
  let := hB
  have hbmap : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg ChapterB.baumann (map_subgroupOf_eq_of_le hH.1.1.2))
  have hnB := (ChapterB.baumann (S : Subgroup H)).le_normalizer_map H.subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hbmap] at hnB
  exact hH.1.2 (hnB.trans h.baumann_normalizer_le)

theorem hstar_thompson_moves_omega_orbit
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H) ≤ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) :=
  ChapterE.ThompsonAction.thompson_moves_of_noncentral_reduced_baumann_not_normal
    (T.subtype hH.1.1.2) (h.hstar_minimal_parabolic hH) _
    (h.hstar_omega_orbit_reduced hH)
    (hstar_omega_orbit_centralizer_proper hH hZH) (h.hstar_baumann_not_normal hH)

theorem hstar_residual_eq_thompson_commutator
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pResidual 2 H =
      ⁅pResidual 2 H, elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆ := by
  let S := T.subtype hH.1.1.2
  have hJ := h.hstar_thompson_moves_omega_orbit hH hZH
  have hU := h.hstar_omega_orbit_reduced hH
  apply ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor S
    (h.hstar_minimal_parabolic hH) _ (sSup_le fun _ hA => hA.1)
    ((S : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  exact fun hc => hJ (hc.trans (le_centralizer_iff.mp hU.le_centralizer_pCore))

end RankOneGeneric.Input

namespace Hypothesis611
variable {M V : Subgroup G}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem maximal_eq_normalizer_L : M = normalizer (L : Set G) := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes_L) (le_componentOrbit L T)
  have he := hu.normalizer_unique M h.maximal
  rw [horbit] at he
  exact he (sup_le h.L_le h.sylow_le)

theorem rankOneInput (hout : Chapter3.HasMaximalOutside T M) :
    RankOneGeneric.Input KnownSimple.IsKnownSimple T L V n := by
  have he := h.maximal_eq_normalizer_L
  exact ⟨h.simpleQTKE, h.local_mem, h.n_gt_one, h.quotient_model,
    he ▸ h.maximal, h.sylow_normalizes_L, h.V_mem, h.nontrivial_action, he ▸ hout⟩

theorem hstar_residual_eq_thompson_commutator
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pResidual 2 H =
      ⁅pResidual 2 H, elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆ := by
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  exact (h.rankOneInput hout).hstar_residual_eq_thompson_commutator hH' hZH


/-- E.2.3 alternatives on the literal intrinsic omega orbit. -/
theorem e23_sylow_or_paired
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
    letI := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    ChapterE.ThompsonAction.SourceSylowAlternative S
      (RankOneGeneric.Input.hstar_minimal_parabolic
        (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)) ∨
      ChapterE.ThompsonAction.SymmetricFivePairSource S U q hq hk := by
  let hinput := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hinput.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter3.sqtk_of_mem_H h.simpleQTKE hH'.1.1.1
  exact ChapterE.ThompsonAction.source_sylow_or_paired_five hsq S
    (hinput.hstar_minimal_parabolic hH') U hU
    (hinput.hstar_thompson_moves_omega_orbit hH' hZH)

/-- The literal H-star orbit either centralizes the intrinsic omega-center or
    enters the E.2.3 alternatives.  This is the branch interface used by the
    solvable and nonsolvable source assemblies. -/
theorem hstar_centralizes_or_e23
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ∨
    (let S := T.subtype hH.1.1.2
     let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
     letI := (RankOneGeneric.Input.hstar_omega_orbit_reduced
       (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
     letI := (RankOneGeneric.Input.hstar_omega_orbit_reduced
       (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
     let C := centralizer (U : Set H)
     let q := QuotientGroup.mk' C
     let hq := QuotientGroup.mk'_surjective C
     let hk := QuotientGroup.ker_mk' C
     ChapterE.ThompsonAction.SourceSylowAlternative S
       (RankOneGeneric.Input.hstar_minimal_parabolic
         (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)) ∨
       ChapterE.ThompsonAction.SymmetricFivePairSource S U q hq hk) := by
  by_cases hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ = ⊥
  · left
    rw [commutator_comm] at hZH
    exact (commutator_eq_bot_iff_le_centralizer.mp hZH)
  · right
    exact h.e23_sylow_or_paired hout hH hZH


end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
