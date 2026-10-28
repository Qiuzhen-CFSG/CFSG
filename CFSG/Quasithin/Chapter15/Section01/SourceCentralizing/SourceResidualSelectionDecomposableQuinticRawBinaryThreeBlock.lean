module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock

/-!
# The whole binary-three block on the original raw component

The actual C.2.7 star comparison identifies L/O₂(L) with SL₃(2).
The original marked intersection supplies the odd-index MS radical. Its
normalization by T puts the original central-involution seed inside Q₁.
The seed is central in the actual Sylow subgroup of LQ₁, so its singleton
centralizer overgroup excludes the doubled-module and nonabelian MS escape
alternatives. The entire original L is therefore a natural binary-three block.

The internal catalogue import reuses only its intrinsic MS block-or-escape
lemma, whose statement has no component record. No Case-I record, whole-M
generation, or global residual-centralization premise is constructed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher PerfectCentralCovering
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

private noncomputable def raw_binaryThree_cover {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    (e : starImage L R L ≃* Matrix.PSL3Two.SL) :
    Cover (L ⧸ pCore 2 L) Matrix.PSL3Two.SL where
  toMonoidHom := e.toMonoidHom.comp (coreToStar hi.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective hi.normalizes)
  isPerfect := hi.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source hi

/-- The actual binary-three star map has no residual central covering kernel. -/
theorem raw_binaryThree_coreToStar_bijective {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    (e : starImage L R L ≃* Matrix.PSL3Two.SL) :
    Function.Bijective (coreToStar hi.normalizes) := by
  let c := raw_binaryThree_cover hi e
  let ec := Matrix.PSL3Two.centralCoverEquiv c (pCore_quotient_pCore_eq_bot 2)
  refine ⟨?_,coreToStar_surjective hi.normalizes⟩
  intro x y hxy
  apply ec.injective
  rw [Matrix.PSL3Two.centralCoverEquiv_apply,Matrix.PSL3Two.centralCoverEquiv_apply]
  exact congrArg e hxy

omit [Finite G] in
private theorem raw_binaryThree_smallQuotient {L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) : SmallRankTwoQuotient L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    exact e.map_eq_one_iff.mp
      (Matrix.PSL3Two.center_eq_bot.le ((centerCongr e ⟨x,hx⟩).property))
  let ez : (L ⧸ centralPreimage (pCore 2 L)) ≃* Matrix.PSL3Two.SL :=
    (centralPreimageQuotientEquiv (pCore 2 L)).trans
      (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e)
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  exact Or.inl ⟨ez.trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

private theorem raw_seed_le_marked_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {Mc Z1 : Subgroup G} (hZT : Z1 ≤ (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hQne : (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 ≠ ⊥)
    (hn : (T : Subgroup G) ≤ normalizer ((centralizer (Z1 : Set G) ⊓ Mc : Subgroup G) : Set G)) :
    centralInvolutions T ≤ (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  let Q := N.pCoreIn 2
  let J := N ⊔ (T : Subgroup G)
  have hJnorm : J ≤ normalizer (N : Set G) := sup_le N.le_normalizer hn
  have hJQ : J ≤ normalizer (Q : Set G) := hJnorm.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hQJ : Q ≤ J := (map_subtype_le _).trans le_sup_left
  have hH : J ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,(show (T : Subgroup G) ≤ J from le_sup_right)⟩
    intro hb
    exact hQne (bot_unique ((le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 N) hQJ hJQ).trans_eq hb))
  have hZJ : centralInvolutions T ≤ J.pCoreIn 2 :=
    (centralInvolutions_le_omegaCore hG T hH).trans
      (map_mono (show omegaOneCenterAmbient (pCore 2 J) ≤ pCore 2 J from
        fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1))
  have hZN : centralInvolutions T ≤ N := by
    refine le_inf ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le hZT)) ?_
    exact ((centralInvolutions_le_centralizer_sylow T).trans
      (centralizer_le (centralInvolutions_le_sylow T))).trans (centralizer_le_partner T hu)
  have hnorm : N ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (show N ≤ J from le_sup_left).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  exact (le_inf hZJ hZN).trans (le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 J).to_le (show J.pCoreIn 2 ⊓ N ≤ J.pCoreIn 2 from inf_le_left))
    inf_le_right ((le_inf hnorm N.le_normalizer).trans inf_normalizer_le_normalizer_inf))

/-- The actual original C.2.7 binary-three row reconstructs the entire L,
using the original seed, radical and T-normalized marked intersection. -/
theorem PreparedChosenModule.raw_binaryThree_block_of_original_input
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
    (e : starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ≃* Matrix.PSL3Two.SL) :
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
  let ec := (MulEquiv.ofBijective (coreToStar hi.normalizes)
    (raw_binaryThree_coreToStar_bijective hi e)).trans e
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

end CFSG.Quasithin.Chapter15.Section01
