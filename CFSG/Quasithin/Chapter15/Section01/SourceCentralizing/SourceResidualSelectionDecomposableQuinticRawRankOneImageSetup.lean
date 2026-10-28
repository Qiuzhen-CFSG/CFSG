module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalFixed

/-! The actual rank-one normalizer retains the original seed, residual,
minimal parabolic and a noncentral vector in the original Thompson alpha. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB ChapterC
open ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.raw_rankOne_normalizer_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let K := (L.subgroupOf H).map q
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      K ≃* Matrix.SpecialLinearGroup (Fin 2) F →
      ∃ (P : Sylow 2 H) (hr : IsPReduced 2 U),
        letI := hr.elementary
        let ρ := NormalElementaryQuotient.representation U q
          (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
        let J := offenderSubgroup ρ
        (P : Subgroup H).map H.subtype = R ∧ generalizedFitting H = pCore 2 H ∧
          pResidual 2 H = L.subgroupOf H ∧
          U ≤ normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) ∧
          ¬elementaryAbelianMaxJ (P : Subgroup H) ≤ C ∧
          IsMinimalParabolicOver P ⊤ ∧ IsFFModule ρ ∧
          IsQuasisimple (generalizedFitting J) ∧
          Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp J.subtype)
            (generalizedFitting J)) := by
  dsimp only
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let K := (L.subgroupOf H).map q
  intro F _ _ _ e
  obtain ⟨_,_,⟨P,hP⟩,hJRS,hZR⟩ :=
    h.raw_component_thompson hG T hM hJ hu hZ hL hq hf hout houtM
  obtain ⟨hr,hcore,hfit,hquasi,hff,hKJ,hclass⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hL hq hf hout houtM
  let := hr.elementary
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  let L0 := L.subgroupOf H
  let : L0.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer inf_le_right)
  have hL0 : L0.IsCComponent := hL.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let : Group.IsPerfect L0 := hL0.perfect
  have hPS : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  have hgen : L0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hfitH : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_sup_le 2 L R (hf ▸ centralizer_generalizedFitting_le L)
        (T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left)))
        inf_le_right)
  have hres : pResidual 2 H = L0 :=
    (residuals_of_perfect_normal_sup_twoGroup L0 (P : Subgroup H) P.isPGroup' hgen).1
  have hseed : U ≤ normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) := by
    apply normalClosure_mono
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨?_,?_,?_⟩
    · rw [hPS]
      exact hZR hz
    · apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.1
    · intro x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        (show (x : G) ∈ (T : Subgroup G) from ((hP ▸ mem_map_of_mem H.subtype hx).1).1))
  have hmove : ¬elementaryAbelianMaxJ (P : Subgroup H) ≤ C := by
    intro hj
    have hJQ : elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H := by
      rw [hcore,←hPS]
      exact le_inf (sSup_le fun _ hA => hA.1) hj
    have he := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : L0 ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
      rw [←he]
      exact le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    have hm := (map_mono (f := H.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS,
      (h.caseI_marked_thompson_control hG T hM hJ hZ).1] at hm
    exact houtM (hm.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)
  obtain ⟨f,ec,hfval,hec,hfs,_,heker,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hL hq hf hout houtM
  let i : L0 ≃* L := subgroupOfEquivOfLe le_sup_left
  let f0 := e.toMonoidHom.comp (f.comp i.toMonoidHom)
  have hfs0 : Function.Surjective f0 := e.surjective.comp (hfs.comp i.surjective)
  have hi : IsPGroup 2 i.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr i.injective]
    exact IsPGroup.of_bot
  have hfk : f0.ker ≤ (frattini (L0 ⧸ pCore 2 L0)).comap (QuotientGroup.mk' (pCore 2 L0)) := by
    rw [←i.toMonoidHom.comap_frattini_pCore_of_pKernel i.surjective hi]
    intro x hx
    let := hq
    apply center_le_frattini_of_isPerfect
    apply heker
    change ec (QuotientGroup.mk' (pCore 2 L) (i x)) = 1
    rw [hec]
    apply e.injective
    exact hx.trans (map_one e.toMonoidHom).symm
  have hmin := minimal_over_normal_rankOne_frattini F L0 P hgen f0 hfs0 hfk
  let : J.Normal := offenderSubgroup_normal ρ
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  let : IsElementaryAbelian 2 A := hA.1.2
  have hshape : IsQuasisimple (generalizedFitting (H ⧸ C)) := hfit ▸ hquasi
  have hF := generalizedFitting_normal_eq_of_quasisimple_or_three hr.quotient_pCore_eq_bot
    (Or.inl hshape) J A (IsElementaryAbelian.isPGroup 2 A) hA.1.1 (hA.le_offenderSubgroup ρ)
  have hfitJ : generalizedFitting J = K.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show K ≤ J from hKJ),hF]
    exact hfit.symm
  let : IsQuasisimple K := hquasi
  have hqK : IsQuasisimple (K.subgroupOf J) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show K ≤ J from hKJ)).symm
  exact ⟨P,hr,hP,hfitH,hres,hseed,hmove,hmin,hff,hfitJ.symm ▸ hqK,hfitJ.symm ▸ hclass⟩

theorem PreparedChosenModule.raw_rankOne_fixed_witness
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hf : generalizedFitting L = pCore 2 L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let C := centralizer (U : Set H)
    let K := (L.subgroupOf H).map (QuotientGroup.mk' C)
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      K ≃* Matrix.SpecialLinearGroup (Fin 2) F →
      ∃ u ∈ (⁅U,L.subgroupOf H⁆).map H.subtype,
        u ∈ thompsonAlpha S ∧ u ∉ centralizer (L : Set G) := by
  dsimp only
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  intro F _ _ _ e
  obtain ⟨P,hr,hP,_,hres,_,hmove,hmin,_,hqs,⟨c⟩⟩ :=
    h.raw_rankOne_normalizer_setup hG T hM hJ hu hZ hZne hL hq hf hout houtM F e
  let := hr.elementary
  have hw := quasisimple_rankOne_fixed_noncentral P hmin U hr hmove q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs c
  let W := (⁅U,pResidual 2 H⁆ : Subgroup H)
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_le (show W ≤ U from commutator_le_left U _)
  obtain ⟨u,huW,huc⟩ := SetLike.not_le_iff_exists.mp hw
  have hWP : W ≤ (P : Subgroup H) :=
    (commutator_le_left U _).trans (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P))
  let : IsElementaryAbelian 2 (W ⊓ centralizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) : Subgroup H) :=
    IsElementaryAbelian.of_le (show W ⊓ centralizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ≤ W from inf_le_left)
  have hua : u ∈ thompsonAlpha (P : Subgroup H) :=
    elementary_centralizer_maxJ_le_omegaCenter (P : Subgroup H) _
      (inf_le_left.trans hWP) inf_le_right huW
  have hJRS := (h.raw_component_thompson hG T hM hJ hu hZ hL hq hf hout houtM).2.2.2.1
  have hα : (thompsonAlpha (P : Subgroup H)).map H.subtype = thompsonAlpha S := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS]
  refine ⟨u,?_,hα ▸ mem_map_of_mem H.subtype hua,?_⟩
  · change (u : G) ∈ (⁅U,L.subgroupOf H⁆ : Subgroup H).map H.subtype
    rw [←hres]
    exact mem_map_of_mem H.subtype huW.1
  · intro hc
    apply huc
    intro k hk
    apply Subtype.ext
    exact hc k (show k ∈ L.subgroupOf H from hres ▸ hk)

end CFSG.Quasithin.Chapter15.Section01
