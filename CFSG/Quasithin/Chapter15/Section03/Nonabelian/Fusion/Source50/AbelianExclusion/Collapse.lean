module
public import Theory.GroupTheory.PResidual.FullActorCore
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions

/-!
# The core-collapse contradiction in 15.3.52

The ordinary alternative identifies O₂(Y) with C_Y(V). Once C_U(V) is
contained in V, the full-commutator identity Y=[Y,U] forces O₂(Y)≤V.
The original strict containment in 15.3.9 gives the contradiction.

Source: Aschbacher–Smith, Lemma 15.3.52, printed p.1145.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem false_of_original_small_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (ho : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V)
    (hUT : closureU d.Z d.ZS ≤ (d.T : Subgroup G))
    (hfull : d.Y = ⁅d.Y, closureU d.Z d.ZS⁆)
    (hsmall : closureU d.Z d.ZS ⊓ centralizer (d.V : Set G) ≤ d.V) : False := by
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hQY : d.Y.pCoreIn 2 ≤ d.Y := pCoreIn_le 2 d.Y
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal d.M d.Mc)
  have hMQ : d.M ≤ normalizer (d.Y.pCoreIn 2 : Set G) :=
    hMY.trans (normalizer_le_normalizer_characteristic_image d.Y (pCore 2 d.Y))
  have hQV : d.Y.pCoreIn 2 ≤ centralizer (d.V : Set G) := ho.1.le.trans inf_le_right
  have hZV : d.Z ≤ d.V := le_conjugateSpanBy _ _
  have hQU : d.Y.pCoreIn 2 ≤ normalizer (closureU d.Z d.ZS : Set G) :=
    (hQV.trans (centralizer_le hZV)).trans (H_normalizes_closureU d.Z d.ZS)
  have hodd : Odd ((d.Y.pCoreIn 2).subgroupOf d.Y).index := by
    have hQ : (d.Y.pCoreIn 2).subgroupOf d.Y = pCore 2 d.Y := by
      rw [pCoreIn, ← comap_subtype, comap_map_eq_self_of_injective d.Y.subtype_injective]
    obtain ⟨e⟩ := ho.2.1
    rw [hQ, index_eq_card, Nat.card_congr e.toEquiv]
    norm_num [ThreeAlternatives.ElementaryNine, Nat.card_prod, Nat.card_zmod]
  have hle := normal_two_hall_le_of_small_fixed d.M (d.Y.pCoreIn 2) d.Y
    (closureU d.Z d.ZS) d.V (hQY.trans hYM) hYM (hUT.trans d.sylow_le)
    (localModule_le d.T d.sylow_le) hMQ d.action.normalizes hQY
    (isPGroup_pCoreIn 2 d.Y) hodd (residualY_isPPerfect d.M d.Mc)
    hfull.symm hQU hQV hsmall
  obtain ⟨hne, _, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact (not_le_of_gt (source_lemma_15_3_9_of_orthogonal_action hG d.T hempty
    d.action hM hu hmany hne).1) hle

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
