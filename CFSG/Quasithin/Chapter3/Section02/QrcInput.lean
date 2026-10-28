module

public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup

/-!
# The genuine qrc input supplied by the Fundamental Setup

The proved local reducedness and Sylow centralizer equality supply the
module clauses of Hypothesis 3.1.5. Its case (I) is normalization of the
two-residual L₀ by H∩M, which follows from M=N_G(L₀). Source uniqueness
excludes the common-normal alternative, giving the actual D.1.1 qrc
configuration for every original H in H*(T,M).

This constructs the hypotheses used by source 3.1.8; it does not assume
or prove the separate qrc rank bounds or Baumann alternatives of 3.1.6–8.
Source: Aschbacher–Smith, Lemma 3.2.2(9), Theorem 3.1.8,
combined manuscript of 1 March 2004, printed pp.576,579.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G]

/-- The actual internal conjugation image is reduced whenever the
original elementary normal subgroup is reduced. -/
theorem internalActionImage_core_of_reduced
    (H V : Subgroup G) (hVH : V ≤ H) (hn : H ≤ normalizer (V : Set G))
    (hr : IsPReduced 2 (V.subgroupOf H)) :
    pCore 2 (ChapterD.internalActionImage H V hn) = ⊥ := by
  let := hr.normal
  let f := ChapterD.UniqueFactor.actionHom H V hn
  have hk : f.ker = centralizer (V.subgroupOf H : Set H) := by
    rw [ChapterD.UniqueFactor.actionHom_ker]
    ext h
    constructor
    · intro hh v hv
      exact Subtype.ext (hh v hv)
    · intro hh v hv
      exact congrArg (fun h : H => (h : G)) (hh ⟨v, hVH hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (ChapterD.UniqueFactor.actionQuotientEquiv H V hn)
  have hm := pCore_map_iso 2 e
  rw [hr.quotient_pCore_eq_bot, Subgroup.map_bot] at hm
  exact hm.symm

namespace FundamentalSetup
variable [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The original FSU yields Hypothesis 3.1.5 for every H in H*(T,M). -/
theorem qrcHypotheses
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Chapter3.QrcHypotheses T D.maximalLocal (localJoin T L) H D.moduleSubgroup := by
  refine ⟨le_sup_right, (D.lemma_3_2_3_uniqueness h127).2.1, hH,
    D.module_le_core.trans (pCoreIn_le 2 _), D.join_normalizes_module,
    D.module_elementary, ?_, (D.sylow_centralizer_module h127).symm, Or.inl ?_⟩
  · exact internalActionImage_core_of_reduced _ _
      (D.module_le_core.trans (pCoreIn_le 2 _)) D.join_normalizes_module
      (D.module_reduced h127)
  · have he := embedded_pResidual_join_pGroup (localOrbit T L) (T : Subgroup G)
      ((pResidual_eq_top_iff 2 _).mp D.orbit_residual) T.isPGroup'
      (le_normalizer_componentOrbit L T)
    rw [he]
    exact inf_le_right

/-- The genuine source uniqueness excludes every common-normal subgroup
in the qrc configuration attached to the original FSU. -/
theorem qrcConfiguration
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ChapterD.QRCConfiguration (localJoin T L) H (T : Subgroup G) D.moduleSubgroup := by
  have hq := D.qrcHypotheses h127 hH
  exact hq.toQRCConfiguration
    (hq.no_common_normal (D.lemma_3_2_3_uniqueness h127).2.2)

end FundamentalSetup
end CFSG.Quasithin.Chapter3.Section02
