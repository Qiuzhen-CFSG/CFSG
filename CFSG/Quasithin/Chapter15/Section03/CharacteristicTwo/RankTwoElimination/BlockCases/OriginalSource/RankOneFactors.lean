module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualDirections
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneFourGeometry
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# The actual residual factors for the field-four component

The moving plane identifies Y_L with the residual centralizer of the
complementary plane. Its S-invariance gives S-invariance of L by uniqueness
of the relative C-component over Y_L. The genuine rank-two quotient then
identifies Y_C with the other coordinate factor. All premises are discharged
in the original ambient source consumer.

Source: Aschbacher–Smith15.3.18, printed pp.1126–1127.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem le_twoResidual_of_perfect {A B : Subgroup G}
    (hAB : A ≤ B) (hA : IsPPerfect 2 A) : A ≤ Stellmacher.twoResidualAmbient B := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  have h := embedded_pResidual_mono 2 hAB
  rwa [(pResidual_eq_top_iff 2 A).mpr hA, ← MonoidHom.range_eq_map, range_subtype] at h

/-- The actual moving plane identifies its normal two-perfect cubic actor
with the residual centralizer of the complementary plane. -/
theorem residual_eq_plane_factor (d : LocalData G) (A : Subgroup G)
    (hAY : A ≤ d.Y) (hAn : (A.subgroupOf d.Y).Normal) (hAp : IsPPerfect 2 A)
    (hA3 : 3^(Nat.card A).factorization 3 = 3)
    (h7 : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j) (he : ⁅d.V,A⁆ = d.action.plane i) :
    A = centralizingFactor d.Y (d.action.plane j) := by
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
  have hAj := perfect_normalizes_planes d.action (hAY.trans hYM) hAp j
  have hAc : A ≤ centralizer (d.action.plane j : Set G) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf ((commutator_mono (d.action.plane_le j) le_rfl).trans he.le)
      (le_normalizer_iff_commutator_le_left.mp hAj)).trans
      (natural_planes_disjoint d.action hij).le_bot
  let C := centralizingFactor d.Y (d.action.plane j)
  have hAC : A ≤ C := le_twoResidual_of_perfect (le_inf hAY hAc) hAp
  have hCY : C ≤ d.Y := centralizingFactor_le_left _ _
  let f := d.action.actor.comp (inclusion hYM)
  have hmap (B : Subgroup G) (hBY : B ≤ d.Y) :
      (B.subgroupOf d.Y).map f = d.action.image B := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨inclusion hYM b,hb,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨⟨b,hBY hb⟩,hb,he⟩
  have hk : IsPGroup 2 f.ker := by
    rw [residualY_actor_ker_eq_twoCore d.action h7 h9]
    exact pCore_isPGroup
  have hCcard : Nat.card ((C.subgroupOf d.Y).map f) = 3 := by
    rw [hmap C hCY]
    exact (residualY_fullActionCoordinateFacts d.action h7).image_card j
  have hApart : 3^(Nat.card ((A.subgroupOf d.Y).map f)).factorization 3 = 3 := by
    rw [threePart_map_of_twoGroup_kernel f hk,
      Nat.card_congr (subgroupOfEquivOfLe hAY).toEquiv]
    exact hA3
  have hAcard : Nat.card ((A.subgroupOf d.Y).map f) = 3 := by
    have hd : Nat.card ((A.subgroupOf d.Y).map f) ∣ 3 :=
      hCcard ▸ card_dvd_of_le (map_mono (comap_mono hAC))
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hh | hh
    · change 3^(Nat.card ((A.subgroupOf d.Y).map f)).factorization 3 = 3 at hApart
      rw [hh] at hApart
      norm_num at hApart
    · exact hh
  let : (A.subgroupOf d.Y).Normal := hAn
  let : (C.subgroupOf d.Y).Normal := centralizingFactor_normal
    (perfect_normalizes_planes d.action hYM (residualY_isPPerfect _ _) j)
  have hpA : IsPPerfect 2 (A.subgroupOf d.Y) := hAp.of_surjective
    (subgroupOfEquivOfLe hAY).symm.toMonoidHom (subgroupOfEquivOfLe hAY).symm.surjective
  have hpC : IsPPerfect 2 (C.subgroupOf d.Y) := (centralizingFactor_isPPerfect _ _).of_surjective
    (subgroupOfEquivOfLe hCY).symm.toMonoidHom (subgroupOfEquivOfLe hCY).symm.surjective
  have hh := eq_of_normal_twoPerfect_of_map_eq f hk (A.subgroupOf d.Y) (C.subgroupOf d.Y)
    hpA hpC (eq_of_le_of_card_ge (map_mono (comap_mono hAC)) (by rw [hAcard,hCcard]))
  have hm := congrArg (map d.Y.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hCY] using hm
private theorem unique_component_of_not_le_core {K B : Subgroup G}
    (hK : K.IsCComponent) (hBK : B ≤ K) (hB : ¬ B ≤ K.pCoreIn 2)
    [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hcenter : center (K ⧸ pCore 2 K) = ⊥) :
    ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K := by
  intro D hD hBD
  by_contra hne
  have hKD : K ≤ normalizer (D : Set G) :=
    (le_cComponentLayer hK).trans (cComponentLayer_le_normalizer hD)
  let N := D.subgroupOf K
  let : N.Normal := normal_subgroupOf_of_le_normalizer hKD
  have hproper : N ≠ ⊤ := by
    intro ht
    have hle : K ≤ D := fun k hk => show (⟨k,hk⟩ : K) ∈ N from ht ▸ mem_top _
    exact hne (hK.eq_of_le hD hle).symm
  let : Group.IsSolvable N := hK.isSolvable_of_subnormal_lt_top
    (inferInstance : N.Normal).isSubnormal hproper
  let q := QuotientGroup.mk' (pCore 2 K)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  have hqN : N.map q = ⊥ := by
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hc | ht
    · exact le_bot_iff.mp (hc.trans hcenter.le)
    · have hs : Function.Surjective (q.comp N.subtype) := by
        intro z
        obtain ⟨n,hn,he⟩ := (show z ∈ N.map q from ht ▸ mem_top z)
        exact ⟨⟨n,hn⟩, he⟩
      have hsol : Group.IsSolvable (K ⧸ pCore 2 K) := Group.isSolvable_of_surjective hs
      let : IsSimpleGroup ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) :=
        Theory.GroupTheory.IsQuasisimple.simple
      let : Nontrivial (K ⧸ pCore 2 K) :=
        (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K))).nontrivial
      exact (Group.IsPerfect.not_isSolvable (K ⧸ pCore 2 K) hsol).elim
  have hNcore : N ≤ pCore 2 K := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hqN
  apply hB
  intro b hb
  exact mem_map.mpr ⟨⟨b,hBK hb⟩, hNcore (hBD hb), rfl⟩

omit [Finite G] in
private theorem component_quotient_center (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :
    center (c.L ⧸ pCore 2 c.L) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  have hm := (centerCongr e) ⟨x,hx⟩ |>.property
  have he : e x = 1 := mem_bot.mp ((alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))) ▸ hm)
  simpa using he

/-- The residual moving V belongs to a unique C-component of J(I).
The uniqueness is proved using the actual simple two-core quotient; it is
not an extra local hypothesis. -/
theorem naturalFour_component_unique_over_YL (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5))
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥) :
    ∀ D : Subgroup (Stellmacher.elementaryAbelianMaxJ I), D.IsCComponent →
      (YL d c.L).subgroupOf (Stellmacher.elementaryAbelianMaxJ I) ≤ D →
      D = c.L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I) := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  let K := c.L.subgroupOf J
  let eK : K ≃* c.L := subgroupOfEquivOfLe c.le_thompson
  let eQ : (K ⧸ pCore 2 K) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let := c.core_quotient_quasisimple
  let : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv eQ.symm
  have hcenter : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply eQ.injective
    have hm := (centerCongr eQ) ⟨x,hx⟩ |>.property
    have he : eQ x = 1 := mem_bot.mp (component_quotient_center d c e ▸ hm)
    simpa using he
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  apply unique_component_of_not_le_core c.component (comap_mono hAL) _ hcenter
  intro hbad
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply le_trans _ hcore
  intro a ha
  have haJ : a ∈ J := c.le_thompson (hAL ha)
  obtain ⟨k,hk,hka⟩ := hbad (show (⟨a,haJ⟩ : J) ∈ (YL d c.L).subgroupOf J from ha)
  have hmap := mem_map_of_mem eK.toMonoidHom hk
  rw [pCore_map_iso] at hmap
  refine mem_map.mpr ⟨eK k,hmap,?_⟩
  exact congrArg Subtype.val hka

/-- Normalization of the moving residual forces normalization of its unique
relative C-component. Only J(I), not the ambient group, carries the component. -/
theorem naturalFour_component_normalized_of_YL (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5))
    (hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G))
    (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥)
    (hS : d.S ≤ normalizer (YL d c.L : Set G)) :
    d.S ≤ normalizer (c.L : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  have hSJ : d.S ≤ normalizer (J : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ I).map (MulAut.conj s).toMonoidHom = _
    rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv]
    have hi : I.map (MulAut.conj s).toMonoidHom = I :=
      mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer (hI.1.2 (mem_sup_right hs)))
    exact congrArg Stellmacher.elementaryAbelianMaxJ hi
  have hAL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  apply le_normalizer_iff.mpr
  intro s hs l hl
  let eJ : MulAut J := J.normalizerMonoidHom ⟨s,hSJ hs⟩
  have he : (c.L.subgroupOf J).map eJ.toMonoidHom = c.L.subgroupOf J := by
    apply naturalFour_component_unique_over_YL d c e hcore hne _ (c.component.map_equiv eJ)
    intro b hb
    have hpre : (eJ.symm b : G) ∈ YL d c.L := by
      have hm := (hS (d.S.inv_mem hs) b).mp hb
      change (↑((J.normalizerMonoidHom ⟨s,hSJ hs⟩)⁻¹ b) : G) ∈ YL d c.L
      rw [← map_inv]
      exact hm
    exact mem_map.mpr ⟨eJ.symm b,hAL hpre,eJ.apply_symm_apply b⟩
  have hm := mem_map_of_mem eJ.toMonoidHom
    (show (⟨l,c.le_thompson hl⟩ : J) ∈ c.L.subgroupOf J from hl)
  rw [he] at hm
  exact hm

private theorem normalizes_section_residual {Y L A : Subgroup G}
    (hAY : A ≤ normalizer (Y : Set G)) (hAL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer (ComponentIntersection.centralizerResidual Y L : Set G) := by
  have hcore := normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hsection : A ≤ normalizer (Chapter4.sectionCentralizer L : Set G) :=
    commutatorPreimage_normalized (normalizer (L : Set G)) L (L.pCoreIn 2) A
      hcore (hAL.trans (normalizer (L : Set G)).le_normalizer) hAL (hAL.trans hcore)
  have hn := (le_inf hAY hsection).trans inf_normalizer_le_normalizer_inf
  rw [ComponentIntersection.centralizerResidual,
    ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

open ChapterA.Section05To06
/-- The two actual component residuals are the two coordinate factors;
S normalizes the selected component. -/
theorem naturalFour_source_residual_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hb : ChapterC.IsL2EvenBlock c.L 2) :
    d.Yplus = d.Y ∧ LinearThree.ResidualPlaneFactors d c.L ∧
      d.S ≤ normalizer (c.L : Set G) := by
  obtain ⟨hfirst,i,j,hij,hi,_⟩ := naturalFour_source_plane_geometry
    hG d hempty hM hu hmany hI htwo hf c hb
  obtain ⟨_,hgen,h9,_,hL3,hC3⟩ := naturalFour_source_local_geometry
    hG d hempty hM hu hmany hI htwo c hb
  obtain ⟨hneMc,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hneMc).1
  have hYL : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hAY : YL d c.L ≤ d.Y :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans hfirst.le
  have hAn : ((YL d c.L).subgroupOf d.Y).Normal := by
    rw [←hfirst]
    exact normal_subgroupOf_of_le_normalizer (ComponentIntersection.normalizes_intersectionResidual hYL)
  have hAX := residual_eq_plane_factor d (YL d c.L) hAY hAn
    (ComponentIntersection.intersectionResidual_isPPerfect _ _) hL3 h7 (hfirst ▸ h9) hij hi
  have hSY := planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice
  have hSL : d.S ≤ normalizer (YL d c.L : Set G) := by
    rw [hAX]
    exact normalizes_centralizingFactor (hfirst ▸ hSY)
      (planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 j)
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
    (LocalData.thompson_component_in c.le_thompson c.component) hrank c.rank_pos
  have hcoreR : c.L.pCoreIn 2 ≤ d.R := by
    intro x hx
    exact h12.2.2 ⟨x,hx,1,(pCoreIn 2 (YL d c.L)).one_mem,mul_one x⟩
  have hcore : c.L.pCoreIn 2 ≤ centralizer (d.V : Set G) := by
    rw [htwo.2.2.2.2.1] at hcoreR
    exact hcoreR.trans inf_le_right
  have hne : ⁅d.V,YL d c.L⁆ ≠ ⊥ := by
    rw [hi]
    intro he
    have hc := d.action.card_plane i
    simp [he] at hc
  obtain ⟨e⟩ := hb.four_quotient_alternatingFive
  have hSN := naturalFour_component_normalized_of_YL d hI c e hcore hne hSL
  have hSC := normalizes_section_residual hSY hSN
  obtain ⟨hdL,hdC⟩ := LinearThree.component_residual_directions d c.L hYL hSL hSC hL3 hC3
  exact ⟨hfirst,LinearThree.residualPlaneFactors_of_first_choice d c.L hfirst h7 h9
    htwo.2.1 hdL hdC hgen,hSN⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
