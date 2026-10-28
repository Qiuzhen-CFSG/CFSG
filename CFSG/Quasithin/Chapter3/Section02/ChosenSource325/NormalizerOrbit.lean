module

public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter3.Section02.ReducedOrbit
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.CentralizerNormalizer

/-!
# The cubic bound on the full normalizer orbit

Put U = V_M, R = C_T(U), and M₀ = N_M(R) in the Fundamental Setup.
The local centralizer identity gives R = O₂(L₀T) ∩ C_G(U), so L₀T
normalizes R and its uniqueness theorem also controls M₀. The Frattini
argument in C_M(U) identifies the literal action images of M₀ and M;
reducedness then gives O₂(M₀) = R. These are the original qrc hypotheses.
The multiple-overgroup hypothesis supplies H*, and source 3.1.6 bounds the
action of M₀. Equality of the action images transports that bound to M.

This argument keeps the Sylow orbit and full normalizer orbit distinct.
Source: Aschbacher--Smith 3.2.5, combined manuscript of 1 March 2004,
printed p.580, using 3.2.2(2),(8) and 3.1.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD ChapterD.UniqueFactor
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G}

/-- The local join normalizes the Sylow centralizer of the full orbit,
using the centralizer identity for the distinct local orbit. -/
theorem normalizerOrbit_localJoin_le (D : FundamentalSetup K T L)
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    localJoin T L ≤ centralizerSylowNormalizer T D.maximalLocal D.fullModule := by
  let J := localJoin T L
  let R := (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)
  have hJM : J ≤ D.maximalLocal := (D.lemma_3_2_3_uniqueness h127).2.1
  have hVU : D.moduleSubgroup ≤ D.fullModule := le_componentOrbit _ _
  have hR : R = J.pCoreIn 2 ⊓ centralizer (D.fullModule : Set G) := by
    rw [← D.sylow_centralizer_module h127]
    exact le_antisymm
      (le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le hVU))) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hJcore : J ≤ normalizer (J.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 J).le_normalizer_map J.subtype
  refine le_inf hJM ?_
  change J ≤ normalizer (R : Set G)
  rw [hR]
  exact (le_inf hJcore ((hJM.trans D.maximalLocal_normalizes_fullModule).trans
    (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- Hypothesis 3.1.5 for the full orbit and N_M(C_T(U)). The Frattini
action-image equality supplies reducedness and the exact two-core. -/
theorem normalizerOrbit_qrcHypotheses (D : FundamentalSetup K T L)
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Chapter3.QrcHypotheses T D.maximalLocal
      (centralizerSylowNormalizer T D.maximalLocal D.fullModule) H D.fullModule := by
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness h127).2.1
  have hn := D.maximalLocal_normalizes_fullModule
  have hTN := sylow_le_centralizerSylowNormalizer T D.maximalLocal D.fullModule hTM hn
  have hred : pCore 2 (internalActionImage D.maximalLocal D.fullModule hn) = ⊥ :=
    internalActionImage_core_of_reduced _ _
      (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer) hn
      (D.fullModule_reduced h127)
  exact ⟨hTN, inf_le_left, hH, (D.fullModule_le_sylow h127).trans hTN,
    inf_le_left.trans hn, D.fullModule_elementary h127,
    centralizerSylowNormalizer_image_reduced T _ _ hTM hn hred,
    centralizerSylowNormalizer_core T _ _ hTM hn hred,
    Or.inr (inf_le_right.trans hn)⟩

/-- Source 3.1.6 bounds the literal M-action on the full normalizer orbit.
The earlier uniqueness input is supplied by Theorems A and C in the
chosen-module application. -/
theorem normalizerOrbit_cubicRatio_le_of_many
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    letI := D.fullModule_elementary h127
    cubicRatio (imageRepresentation D.maximalLocal D.fullModule
      D.maximalLocal_normalizes_fullModule) ≤ 2 := by
  let : IsElementaryAbelian 2 D.fullModule := D.fullModule_elementary h127
  obtain ⟨hM, hJM, hu⟩ := D.lemma_3_2_3_uniqueness h127
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_sup_right.trans hJM
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany D.maximalLocal hM hTM)
  have hne : D.fullModule ≠ ⊥ := fun he => D.module_ne_bot
    (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans he.le))
  have hq := (D.normalizerOrbit_qrcHypotheses h127 hH).source_cubicRatio_le_two
    D.simpleQTKE hM
    (fun N hN hle => hu N hN ((D.normalizerOrbit_localJoin_le h127).trans hle)) hne
  let e := MulEquiv.subgroupCongr (centralizerSylowNormalizer_actionImage_eq T
    D.maximalLocal D.fullModule hTM D.maximalLocal_normalizes_fullModule)
  exact cubicRatio_le_nat_of_equivariant
    (imageRepresentation (centralizerSylowNormalizer T D.maximalLocal D.fullModule)
      D.fullModule (inf_le_left.trans D.maximalLocal_normalizes_fullModule))
    (imageRepresentation D.maximalLocal D.fullModule D.maximalLocal_normalizes_fullModule)
    e.toMonoidHom e.injective (LinearEquiv.refl (ZMod 2) (Additive D.fullModule))
    (fun _ _ => rfl) 2 hq

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
