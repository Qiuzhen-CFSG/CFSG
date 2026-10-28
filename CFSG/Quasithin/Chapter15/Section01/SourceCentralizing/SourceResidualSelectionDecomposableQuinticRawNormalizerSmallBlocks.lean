module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawG2Block
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryThreeBlock
-- Internal reuse is limited to the intrinsic binary MS block-or-escape
-- lemma and the already proved original seed containment.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryThreeBlock
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock

/-!
# Whole small blocks from the actual original normalizer image

The actual core-to-normalizer map is a perfect central cover. Native
small-model cover theorems kill its kernel in the O₂-free core quotient.
The resulting literal full-core marking feeds the original C.2.7 MS pair,
using its marked Sylow and original seed, to reconstruct the whole same L.
The star image is not identified with the normalizer image. No whole-M
generation, residual-centralization or reconstruction callback is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher PerfectCentralCovering
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

private theorem raw_normalizer_small_outside_selected
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) : ¬L ≤ M := by
  intro hLM
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let : Group.IsPerfect (L.subgroupOf (L ⊔ S)) := hlocal.1.perfect
  let i : L.subgroupOf (L ⊔ S) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  exact hi.outside (le_inf hi.component.1
    ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
      (localModule_centralizer_le_partner T M hu)))

private theorem raw_binaryThree_block_of_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hQne : (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hnM : (T : Subgroup G) ≤ normalizer ((centralizer (Z1 : Set G) ⊓ Mc : Subgroup G) : Set G))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (ec : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock L 1 := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let N := H ⊓ Mc
  let Q := N.pCoreIn 2
  let S := (T : Subgroup G) ⊓ H
  let SL := S ⊓ L
  let S0 := SL ⊔ Q
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : S ≤ N := le_inf inf_le_right (inf_le_left.trans hTMc)
  have hQS : Q ≤ S := by
    obtain ⟨P,hP⟩ := hs.restrict hSM inf_le_left
    have hh := map_mono (f := N.subtype) (pCore_isPGroup.le_sylow_of_normal P)
    rwa [hP] at hh
  have hr : MSOddIndexRadical (Q.subgroupOf H) := by
    obtain ⟨P,hP⟩ := hs
    apply msOddIndexRadical_of_first_core hi N inf_le_left le_rfl P
    · intro x hx
      have hxS : x.val ∈ S := by
        change x.val ∈ (T : Subgroup G) ⊓ H
        rw [← hP]
        exact mem_map_of_mem H.subtype hx
      exact hSM hxS
    · rfl
  have hm := Chapter14.Section06.smallMSPair_from_c27 hi hr (raw_binaryThree_smallQuotient ec)
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hZQ := raw_seed_le_marked_core hG T ((hZ.trans inf_le_left).trans hVT) hu hQne hnM
  have hS0S : S0 ≤ S := sup_le inf_le_left hQS
  have hS0N : S0 ≤ normalizer (L : Set G) :=
    sup_le (inf_le_right.trans L.le_normalizer) hi.normalizes
  have hgen : L ⊔ S0 = L ⊔ Q := by
    rw [←sup_assoc,sup_eq_left.mpr (show SL ≤ L from inf_le_right)]
  obtain ⟨P,hP⟩ := hSL
  have hSyl : Chapter1.IsSylowIn 2 S0 (L ⊔ Q) := by
    rw [←hgen]
    exact (T.isPGroup'.to_le (hS0S.trans inf_le_left)).exists_sylow_sup_of_coprime_index
      L S0 hS0N (P : Subgroup L) P.not_dvd_index (hP ▸ le_sup_left)
  have hZomega : centralInvolutions T ≤ FullSieve.SourceInterface.omegaCenterIn S0 := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨mem_sup_right (hZQ hz),
      ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.1,
      fun x hx => centralInvolutions_le_centralizer_sylow T hz x ((hS0S hx).1)⟩
  apply (CaseIComponentData.binaryThree_block_or_normalizer_escape hm ec hSyl le_sup_right).resolve_right
  intro hesc
  apply hesc
  intro l hl
  have hlMc : l ∈ Mc := Chapter15.Section03.InitialSource.centralizer_le_partner T hu (centralizer_le hZomega hl.2)
  exact (N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
    ⟨hi.component.1 hl.1,hlMc⟩


private theorem raw_g2_block_of_core
    (T : Sylow 2 G) {Mc Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (ec : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) : ChapterC.IsG2TwoBlock L := by
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
  exact Chapter14.Section06.g2_block_from_c27 g2Reconstruction_knownSimple hi hr ec


/-- The actual original normalizer-image G₂(2)′ row reconstructs the
whole G₂ block on the same L and Q₁. -/
theorem PreparedChosenModule.raw_normalizer_g2_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    I ≃* commutator (Atlas.G2.Model (ZMod 2)) → ChapterC.IsG2TwoBlock L := by
  dsimp only
  intro e
  have houtM := raw_normalizer_small_outside_selected hG T hempty hM hu hlocal hi
  obtain ⟨_,f,_,_,_,hfs,hfc,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne ⟨hi.component.1,hlocal⟩ hi.quasisimple hi.fitting hi.outside houtM
  let c : Cover (L ⧸ pCore 2 L) (commutator (Atlas.G2.Model (ZMod 2))) :=
    { toMonoidHom := e.toMonoidHom.comp f
      surjective := e.surjective.comp hfs
      isPerfect := hi.quasisimple.toIsPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact hfc }
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup c
  have hz : c.toMonoidHom.ker = ⊥ := bot_unique
    ((show c.toMonoidHom.ker ≤ pCore 2 (L ⧸ pCore 2 L) from
      le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2))
  let ec := MulEquiv.ofBijective c.toMonoidHom
    ⟨c.toMonoidHom.ker_eq_bot_iff.mp hz,c.surjective⟩
  exact raw_g2_block_of_core T hu hs hi ec

/-- The actual original normalizer-image SL₃(2) row reconstructs the
whole natural block, using the original central seed to exclude MS escape. -/
theorem PreparedChosenModule.raw_normalizer_binaryThree_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hQne : (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hTn : (T : Subgroup G) ≤ normalizer
      ((centralizer (Z1 : Set G) ⊓ Mc : Subgroup G) : Set G))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    I ≃* Matrix.PSL3Two.SL → IsSL3EvenBlock L 1 := by
  dsimp only
  intro e
  have houtM := raw_normalizer_small_outside_selected hG T hempty hM hu hlocal hi
  obtain ⟨_,f,_,_,_,hfs,hfc,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne ⟨hi.component.1,hlocal⟩ hi.quasisimple hi.fitting hi.outside houtM
  let c : Cover (L ⧸ pCore 2 L) Matrix.PSL3Two.SL :=
    { toMonoidHom := e.toMonoidHom.comp f
      surjective := e.surjective.comp hfs
      isPerfect := hi.quasisimple.toIsPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact hfc }
  let ec := Matrix.PSL3Two.centralCoverEquiv c (pCore_quotient_pCore_eq_bot 2)
  exact raw_binaryThree_block_of_core hG T hM.1.2 hu h hZ hs
    (ComponentModels.source20_sylow_intersection hlocal) hQne hTn hi ec

end CFSG.Quasithin.Chapter15.Section01
