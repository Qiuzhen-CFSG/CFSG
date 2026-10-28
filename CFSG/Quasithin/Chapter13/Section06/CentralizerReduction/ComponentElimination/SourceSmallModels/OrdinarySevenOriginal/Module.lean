module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreCentralConjugation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
/-!
# The original seed module in the ordinary seven-point branch

The genuine Sylow and characteristic-two conclusions place the seed span
in the elementary core center. Its nontrivial commutator with K is a normal
subgroup of the short module. Short-block irreducibility makes that subgroup
central or the whole module; coprime commutator idempotence excludes the
central alternative. Thus the literal U_K equals [Z(O₂(K)),K], with no
additional representation or carrier-identification hypothesis.

The final theorem constructs this identity, elementary abelianness of W_K,
its containment in T_v and the trivial plus two-core from the original flag
and local configuration. These are the module inputs of the ordinary A₇
replacement in 13.6.22; its local normalizer inputs are separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.7, 13.6.6, 13.6.14 and 13.6.22, printed pp.123 and 928–932.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open ComponentSelection A5Module SourceContainment
open LinearThreeBranch.MSSourceModels LinearThreeBranch.MSSourceModels.SeedCarrier
variable {G : Type*} [Group G] [Finite G] {K L T : Subgroup G} {z v : G}

/-- The source seed commutator is the full short-block commutator module. -/
theorem UK_eq_sourceU_of_short (d : EarlierData K L T z v) (hs : IsShort K) :
    UK K L T z v = sourceU K := by
  have he : sourceU K = (blockU K).map K.subtype :=
    sourceU_eq_of_central K hs.twoPerfect hs.central
  have hU := (d.UK_le_sourceU hs.twoPerfect).trans_eq he
  have hUK : UK K L T z v ≤ K := hU.trans (map_subtype_le _)
  let N := (UK K L T z v).subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  have hN : N ≤ blockU K := by
    intro k hk
    obtain ⟨u, hu, hu'⟩ := hU hk
    exact (K.subtype_injective hu') ▸ hu
  rcases hs.normal_core_dichotomy N hN with hc | hu
  · have hc' : UK K L T z v ≤ centralizer (K : Set G) := by
      intro u hu k hk
      exact congrArg Subtype.val
        (mem_center_iff.mp (hc (show (⟨u, hUK hu⟩ : K) ∈ N from hu)) ⟨k, hk⟩)
    have hid : ⁅UK K L T z v, K⁆ = UK K L T z v :=
      commutator_isPPerfect_idempotent K (WK K L T z v) hs.twoPerfect
        d.WK_isPGroup d.K_normalizes_WK
    exact (UK_ne_bot d.component d.normalizeK
      (hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc'))).elim
  · apply le_antisymm (d.UK_le_sourceU hs.twoPerfect)
    rw [he]
    exact (map_mono hu).trans (map_comap_le _ _)

/-- Construct all four module premises of the ordinary A₇ replacement from
its original flag, local Sylow centralizer and characteristic-two conclusion. -/
theorem module_inputs_of_localConfiguration
    {T : Sylow 2 G} {M V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hblock : IsAlternatingBlock K 7)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    IsElementaryAbelian 2
        (WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) ∧
      WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ≤
        Tv (T : Subgroup G) (markedV d.flag.module) ∧
      pCore 2 (Gplus K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz) = ⊥ ∧
      ⁅WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module), K⁆ =
        ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ := by
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) :=
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central
  have hzOmega : markedZ d.flag.module ∈
      omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.flag.module)) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨hzmem.1, markedZ_mem_Gv d.flag.module⟩, hzmem.2.1,
        fun t ht => hzmem.2.2 t ht.1⟩
  let earlier : EarlierData K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) :=
    ⟨hK, hSylow, hn, hLK, hzOmega, hchar⟩
  exact ⟨SourceContainment.LinearThree.CentralAction.ModuleAlternatives.wk_elementary
      K L (T : Subgroup G) _ _ hK.1.1 hSylow hzOmega hchar,
    earlier.WK_le_Tv,
    SourceContainment.LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
      K L (T : Subgroup G) _ _ hK.1.1 hL hz hSylow,
    UK_eq_sourceU_of_short earlier hblock.2.1⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
