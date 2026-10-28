module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawConstrainedSource
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Reconstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source
public import Theory.SpecificGroups.SU3.TernaryPerfectCover

/-!
# Whole binary G₂ block at the original raw quintic component

The literal C.2.7 comparison is a central perfect cover. Its two-group
kernel is trivial in the full two-core quotient. The original marked
intersection contains the original Sylow subgroup and has exactly the
specified two-core, so it supplies MS2 without a Case-I generation premise.
The whole-block reconstruction retains the original component and its
full natural module; no normalizer-image/star-image identification is used.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- The original central comparison to the derived binary G₂ star is injective. -/
theorem raw_g2_coreToStar_bijective {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    (e : starImage L R L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Function.Bijective (coreToStar hi.normalizes) := by
  let c : Cover (L ⧸ pCore 2 L) (commutator (Atlas.G2.Model (ZMod 2))) := {
    toMonoidHom := e.toMonoidHom.comp (coreToStar hi.normalizes)
    surjective := e.surjective.comp (coreToStar_surjective hi.normalizes)
    isPerfect := hi.quasisimple.toIsPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact coreToStar_ker_central_from_source hi }
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup c
  have hz : c.toMonoidHom.ker = ⊥ := bot_unique
    ((show c.toMonoidHom.ker ≤ pCore 2 (L ⧸ pCore 2 L) from
      le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2))
  have hinj := (MonoidHom.ker_eq_bot_iff c.toMonoidHom).mp hz
  exact ⟨fun _ _ hh => hinj (congrArg e hh), coreToStar_surjective hi.normalizes⟩

/-- The actual raw C.2.7 star row reconstructs the whole original component. -/
theorem raw_g2_block_of_original_input
    (T : Sylow 2 G) {Mc Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (e : starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : ChapterC.IsG2TwoBlock L := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤
      centralizer (Z1 : Set G) ⊓ Mc := le_inf inf_le_right (inf_le_left.trans hTMc)
  obtain ⟨P,hP⟩ := hs
  have hr : MSOddIndexRadical
      (((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).subgroupOf
        (centralizer (Z1 : Set G))) := by
    apply msOddIndexRadical_of_first_core hi (centralizer (Z1 : Set G) ⊓ Mc)
      inf_le_left le_rfl P
    · intro x hx
      exact hSM (hP ▸ mem_map_of_mem (centralizer (Z1 : Set G)).subtype hx)
    · rfl
  let ec := (MulEquiv.ofBijective (coreToStar hi.normalizes)
    (raw_g2_coreToStar_bijective hi e)).trans e
  exact Chapter14.Section06.g2_block_from_c27 g2Reconstruction_knownSimple hi hr ec

end CFSG.Quasithin.Chapter15.Section01
