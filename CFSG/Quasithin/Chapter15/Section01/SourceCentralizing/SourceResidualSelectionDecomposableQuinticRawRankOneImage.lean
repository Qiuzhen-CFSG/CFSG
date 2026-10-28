module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawRankOneImageSetup
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawRankOneImageOrbit
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNoRankOne
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
-- Reuse the original seed-normalizer containment, which has no component record input.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNonblock

/-! Rank-one image reconstruction for the literal original normalizer action.
The noncentral fixed witness and distinct-component separation force Baumann
normalization. Original seed and pair control then reconstruct an actual
natural L2 or alternating-five block. No block is inferred from a group
isomorphism alone, and no whole-M generation or residual premise is assumed. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB ChapterC
open ChapterC.RankOne.ChiProduct.SelectedRankOne ChapterC.RankOne.FiveBlockSource
open ChapterC.GlaubermanNiles ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

private theorem raw_rankOne_chi_of_baumann
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M)
    (hbaum : baumann ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (K : Set G)) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (K : Set G)
    let H := K ⊔ R
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let C := centralizer (U : Set H)
    let I := (K.subgroupOf H).map (QuotientGroup.mk' C)
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      I ≃* Matrix.SpecialLinearGroup (Fin 2) F → IsChiBlock K := by
  dsimp only
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (K : Set G)
  let H := K ⊔ R
  let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  intro F _ _ _ e
  obtain ⟨P,hr,hP,hfitH,hres,hseed,hmove,hmin,hff,hqs,⟨c⟩⟩ :=
    h.raw_rankOne_normalizer_setup hG T hM hJ hu hZ hZne hK hq hf hout houtM F e
  let := hr.elementary
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hHG : H ≤ centralizer (Z1 : Set G) := sup_le hK.1 (inf_le_left.trans inf_le_right)
  have hsqH := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    (hsq.subgroup (H.subgroupOf (centralizer (Z1 : Set G))))
  have hcpu : (baumann (P : Subgroup H)).characteristicNormalizerClosure ≤ M.subgroupOf H := by
    have hBR : baumann S ≤ R := le_inf inf_le_left hbaum
    have hB : baumann R = baumann S := baumann_eq_of_intermediate S R hBR inf_le_left
    have hm : (baumann (P : Subgroup H)).map H.subtype = baumann S := by
      unfold baumann thompsonAlpha
      rw [baumann_map_injective H.subtype H.subtype_injective,hP]
      exact hB
    have hb : baumann (P : Subgroup H) = (baumann S).subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hm,map_subgroupOf_eq_of_le (hBR.trans le_sup_right)]
    rw [hb]
    exact characteristicNormalizerClosure_subgroupOf_le (hBR.trans le_sup_right)
      (h.caseI_marked_thompson_control hG T hM hJ hZ).2.2.1
  have hesc : ¬ pResidual 2 H ≤ M.subgroupOf H := by
    rw [hres]
    intro hh
    apply houtM
    intro k hk
    exact hh (show (⟨k,mem_sup_left hk⟩ : H) ∈ K.subgroupOf H from hk)
  have hqn : q.ker ≠ ⊤ := by
    rw [QuotientGroup.ker_mk']
    intro hz
    apply hmove
    change elementaryAbelianMaxJ (P : Subgroup H) ≤ C
    rw [hz]
    exact le_top
  have hminq := (minimalParabolic_reduced_image P hmin q
    (QuotientGroup.mk'_surjective C) hr.quotient_pCore_eq_bot hqn).2
  have hchi : IsChiBlockIn (pResidual 2 H) := by
    rcases source_offender_quasisimple_rank_one ρ (P.mapSurjective (QuotientGroup.mk'_surjective C))
      hminq hff hr.quotient_pCore_eq_bot hqs c with ⟨F0,hnat⟩ | ⟨efive⟩
    · exact quasisimple_linear_seed_chi_of_baumann_control P hmin U hr hmove
        q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs c.sectionData F0 hnat
        hseed hfitH (M.subgroupOf H) hcpu hesc
    · obtain ⟨efive⟩ := efive
      let W := ⁅U,pResidual 2 H⁆
      have hW := hr.moved U
      let := hW.elementary
      have hmoveW : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
        rwa [hr.centralizer_moved_eq U]
      obtain ⟨q5,hq5,hk5,f,hfs,hfe,hfk⟩ := quasisimple_five_source_marker P hmin U
        hr hmove q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
        hqs c.sectionData efive
      obtain ⟨hcomp,⟨eL⟩⟩ := symmetric_five_residual_component
        (ChapterA.SQTKStructure.a36Input_of_theoremsAC
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
        hsqH P hmin W hW hmoveW q5 hq5 hk5
      have him : (pResidual 2 H).map q5 = alternatingGroup (Fin 5) := by
        rw [map_pResidual_of_surjective 2 q5 hq5,Equiv.Perm.twoResidual_eq_alternating]
      have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
          NormalElementaryQuotient.representation W q5 hq5 hk5 g v = v := by
        intro v hv g hg
        have hv' : v ∈ fixedSpace (NormalElementaryQuotient.representation W q5 hq5 hk5)
            ((pResidual 2 H).map q5) := hfk ▸ hv
        exact hv' ⟨g,him.symm ▸ hg⟩
      have hbT := (h.caseI_marked_thompson_control hG T hM hJ hZ).2.1
      have hBR : baumann (T : Subgroup G) ≤ (P : Subgroup H).map H.subtype := by
        rw [hP,←hbT]
        exact le_inf inf_le_left hbaum
      have hRT : (P : Subgroup H).map H.subtype ≤ (T : Subgroup G) := by
        rw [hP]
        exact inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left)
      have hTne : (T : Subgroup G) ≠ ⊥ := by
        intro hz
        have hPzero : (P : Subgroup H) = ⊥ :=
          ((P : Subgroup H).map_eq_bot_iff_of_injective H.subtype_injective).mp
            (bot_unique (hRT.trans hz.le))
        exact hmin.2 (hPzero ▸ le_normalizer_of_normal)
      obtain ⟨D,hD⟩ := exists_baumann_universal_pair (T : Subgroup G) T.isPGroup' hTne
      have hsrc := external_source_conclusion (T : Subgroup G) H P hBR hRT hfitH
        (pResidual 2 H) hcomp (pResidual_sup_sylow_eq_top P) eL W q5 hq5 hk5 him
        f hfs hfe hfix hmoveW D hD
      rcases hsrc with hc | hn | ⟨hb,ha,_,_,_⟩
      · have hN := CaseIComponentData.central_seed_normalizer_le hu (firstAmbient (T : Subgroup G) D)
          (firstAmbient_ne_bot (T : Subgroup G) T.isPGroup' D)
          (firstAmbient_le_omegaCenter (T : Subgroup G) D)
        have hHC : H ≤ centralizer (firstAmbient (T : Subgroup G) D : Set G) := by
          intro x hx z hz
          obtain ⟨w,hw,rfl⟩ := hc hz
          exact (congrArg H.subtype ((mem_center_iff.mp hw) ⟨x,hx⟩)).symm
        exact (hout (le_inf hK.1 (le_sup_left.trans
          (hHC.trans ((Subgroup.centralizer_le_normalizer _).trans hN))))).elim
      · let B := secondAmbient (T : Subgroup G) D
        have hBH : B ≤ H := (map_subtype_le _).trans (hBR.trans (map_subtype_le _))
        let : (B.subgroupOf H).Normal := hn
        have hnH : H ≤ normalizer (B : Set G) := by
          have hh := (B.subgroupOf H).le_normalizer_map H.subtype
          rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
            map_subgroupOf_eq_of_le hBH] at hh
          exact hh
        have hcB : (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M := by
          rw [←hbT]
          exact (h.caseI_marked_thompson_control hG T hM hJ hZ).2.2.1
        let := D.second_characteristic
        have hnB := (normalizer_le_characteristicNormalizerClosure
          (baumann (T : Subgroup G)) D.second D.second_ne_bot).trans hcB
        exact (houtM (le_sup_left.trans (hnH.trans hnB))).elim
      · exact ⟨hb,Or.inr ⟨5,by decide,ha⟩⟩
  rw [hres] at hchi
  exact RankOne.ChiProduct.chi_of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)) hchi.2

theorem PreparedChosenModule.raw_rankOne_image_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (K : Set G)
    let H := K ⊔ R
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let C := centralizer (U : Set H)
    let I := (K.subgroupOf H).map (QuotientGroup.mk' C)
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      I ≃* Matrix.SpecialLinearGroup (Fin 2) F →
      (∃ n : ℕ, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5 := by
  dsimp only
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (K : Set G)
  let H := K ⊔ R
  let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  intro F _ _ _ e
  obtain ⟨u,huW,hua,huc⟩ :=
    h.raw_rankOne_fixed_witness hG T hM hJ hu hZ hZne hK hq hf hout houtM F e
  have hbaum : baumann S ≤ normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hn
    have hfix : g*u*g⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr (hg.2 u hua).symm
    have huim : u ∈ ((⁅U,K.subgroupOf H⁆).map H.subtype).map (MulAut.conj g).toMonoidHom := by
      rw [←hfix]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom huW
    exact huc (h.raw_component_moved_separation hG T hM hJ hu hZ hZne hK hq hf hout houtM
      g hg.1 hn huim)
  rcases raw_rankOne_chi_of_baumann hG T hM hJ hu h hZ hZne hK hq hf hout houtM hbaum F e
    with hb | ⟨n,hn,hb⟩
  · exact Or.inl hb
  have hn3 : 3 ≤ n := hb.1
  by_cases h5 : 5 ≤ n
  · obtain ⟨ec⟩ := hb.2.2.quotient_iso
    have hz : center (K ⧸ pCore 2 K) = ⊥ := by
      apply map_injective (f := ec.toMonoidHom) ec.injective
      rw [Theory.GroupTheory.FixedElementary.map_center,
        alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)),Subgroup.map_bot]
    obtain ⟨_,f,_,_,_,hfs,hfc,_⟩ :=
      h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hK hq hf hout houtM
    have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
      (bot_unique (hfc.trans hz.le))
    let ei := MulEquiv.ofBijective f ⟨hi,hfs⟩
    have hr : primeRank 3 (alternatingGroup (Fin n)) = 1 := by
      rw [primeRank_equiv 3 ((ec.symm.trans ei).trans e)]
      exact Matrix.SL2.binary_threeRank_eq_one
    have hn6 : n < 6 := by
      by_contra! hn6
      have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank hn6
      rw [hr] at hh
      omega
    have hn5 : n = 5 := by omega
    subst n
    exact Or.inr hb
  · have he : n = 3 := by obtain ⟨k,hk⟩ := hn; omega
    subst n
    obtain ⟨f⟩ := hb.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
      (f := f.toMonoidHom) f.injective
    exact (hK.2.1.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ S from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show K ≤ K ⊔ S from le_sup_left)).injective)).elim

/-- The original residual, control and movement facts exclude every rank-one
model of the actual seed-normalizer image of this same component. -/
theorem PreparedChosenModule.raw_component_normalizer_not_rankOne
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hn : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      A ⊔ ⁅V,A⁆ ≤ normalizer (L : Set G))
    (hmove : let D := M ⊓ centralizer (Z1 : Set G); let A := (pResidual 2 D).map D.subtype
      ⁅L,⁅V,A⁆⁆ ≠ ⊥) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := L ⊔ (S ⊓ normalizer (L : Set G))
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let K := (L.subgroupOf H).map (QuotientGroup.mk' (centralizer (U : Set H)))
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      IsEmpty (K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  dsimp only
  intro F _ _ _
  refine ⟨fun e => ?_⟩
  rcases h.raw_rankOne_image_block hG T hM hJ hu hZ hZne ⟨hL.1,hlocal⟩ hq hf hout houtM F e
    with hb | hb
  · exact h.raw_component_not_linear_two hG T hM hJ hu hZ hZne hSyl hL hlocal hq
      hout houtM hcontrol hbound hI hmove hb
  · exact h.raw_component_not_alternating_five hG T hM hJ hu hZ ⟨hL.1,hlocal⟩ hq
      hout houtM hSyl hn hmove hb

end CFSG.Quasithin.Chapter15.Section01
