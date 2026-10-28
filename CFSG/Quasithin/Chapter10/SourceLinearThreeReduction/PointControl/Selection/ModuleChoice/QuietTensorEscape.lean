module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorNormalClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.MovingSupport

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import Theory.GroupTheory.NormalElementaryNineSection
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Quiet point escape and the normal-residual Suzuki branch

If the local Thompson subgroup centralizes the selected module, source
3.1.8 forces every H-star to centralize Ω₁Z(T). Thus every T-fixed point of
the original full module has an escaping centralizer when there are multiple
maximal two-local overgroups. Together with the preceding section-centralizer
and normal-closure calculations, this proves that G_z is nonsolvable.

When the original X is normal in G_z, its image modulo O₂(G_z) is the
original elementary nine. The proved two-core-free SQTK classification forces
every C-component onto the Suzuki row. The solvability of Aut(E₉) also puts
each such component inside the literal section centralizer Y_z. This provides
an actual component and its two-core quotient, not merely a model tag.

The subsequent Borel/H-star containment and model exclusions in 8.3.7 remain
open, as do tensor-base recognition and the quiet fixed-support conclusions.
Those remain with qt-d-10-nona5-point-selection; final point-control assembly
remains with qt-d-10-nona5-point-control. Source: Aschbacher--Smith 3.1.8(3ii)
and the normal-X branch of 8.3.7, printed pp.724--725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source 3.1.8(3ii): quiet local Thompson action forces H-star to centralize Ω₁Z(T). -/
theorem quiet_hstar_centralizes_omega
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have hu := source_module_nonsolvable_uniqueness D
  have hm := D.lemma_3_2_3_uniqueness hu
  have hz : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hn
    exact (D.qrcHypotheses hu hH).thompson_moves_of_noncentral_omega
      D.simpleQTKE hm.1 hm.2.2 D.module_ne_bot hn hJ
  intro h hh z hzi
  obtain ⟨c,hc,rfl⟩ := hz hzi
  exact (congrArg H.subtype (mem_center_iff.mp hc ⟨h,hh⟩)).symm

/-- Every H-star centralizes the original T-fixed full-module point. -/
theorem quiet_hstar_le_point_centralizer
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ≤ centralizer ({z} : Set G) := by
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hz : z ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hzV,
      elemPow_eq_one_of_isElementaryAbelian z hzV,
      fun t ht => mem_centralizer_singleton_iff.mp (hzT ht)⟩
  exact (quiet_hstar_centralizes_omega D hJ hH).trans
    (centralizer_le (Set.singleton_subset_iff.mpr hz))

/-- Multiple maximal two-local overgroups force the original point centralizer to escape M. -/
theorem quiet_point_centralizer_not_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ¬ centralizer ({z} : Set G) ≤ D.maximalLocal := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (source_maximalOutside_of_many D hmany)
  exact fun hc => hH.1.2 ((quiet_hstar_le_point_centralizer D hJ hzV hzT hH).trans hc)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- If the section centralizer is solvable, the actual normal closure of X is strictly larger than X. -/
theorem quiet_tensor_point_normalClosure_strict_of_solvable_section
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    Group.IsSolvable (commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G))
      d.X (d.X.pCoreIn 2)) → d.X < d.Kz := by
  dsimp only
  intro hsolv
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hNM := quiet_tensor_solvable_point_normalizer_le D hn hJ e hbase hzV hz1 hzT hsolv
  apply lt_of_le_of_ne d.X_le_Kz
  intro he
  have hnorm : d.Gz ≤ normalizer (d.X : Set G) := by
    rw [he]
    exact le_normalizer_conjugateSpanBy d.X d.Gz
  exact quiet_point_centralizer_not_le D hmany hJ hzV hzT
    ((le_inf le_rfl hnorm).trans hNM)

/-- In the normal-X branch, escape excludes solvability of the literal section centralizer. -/
theorem quiet_tensor_normal_point_section_not_solvable
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
      ¬ Group.IsSolvable (commutatorPreimage d.Gz d.X (d.X.pCoreIn 2)) := by
  dsimp only
  intro hnormal hsolv
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have he : d.Gz ⊓ normalizer (d.X : Set G) = d.Gz :=
    inf_of_le_left ((normal_subgroupOf_iff_le_normalizer
      (d.X_le.trans inf_le_right)).mp hnormal)
  have hsolv' : Group.IsSolvable (commutatorPreimage
      (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)) := by
    rwa [he]
  exact (quiet_tensor_point_normalClosure_strict_of_solvable_section
    D hn hmany hJ e hbase hzV hz1 hzT hsolv').ne
    (d.Kz_eq_X_of_normal hnormal).symm

/-- The original quiet tensor point has nonsolvable ambient centralizer. -/
theorem quiet_tensor_point_centralizer_not_solvable
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  intro hsolv
  let := hsolv
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let : Group.IsSolvable d.Gz := hsolv
  let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
  have hY : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective ((commutatorPreimage_le _ _ _).trans inf_le_left))
  have hstrict := quiet_tensor_point_normalClosure_strict_of_solvable_section
    D hn hmany hJ e hbase hzV hz1 hzT hY
  let P : Sylow 3 d.X := Sylow.nonempty.some
  rcases quiet_tensor_point_normalClosure_alternatives D hn e hbase hzV hz1 hzT P with
    he | ⟨K,hK,_⟩
  · exact hstrict.ne he.symm
  · exact hK.2.not_isSolvable inferInstance


private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- Normality identifies the image of X in the ambient two-core quotient with the original elementary nine. -/
theorem quiet_tensor_normal_point_residual_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    Nonempty (((d.X.subgroupOf d.Gz).map (QuotientGroup.mk' (pCore 2 d.Gz))) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  dsimp only
  intro hnormal
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let B := d.X.subgroupOf d.Gz
  have hB : B.IsSubnormal := hnormal.isSubnormal
  let b := subgroupOfEquivOfLe (d.X_le.trans inf_le_right)
  let bq := QuotientGroup.congr (pCore 2 B) (pCore 2 d.X) b (pCore_map_iso 2 b)
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  exact ⟨(hB.quotientCoreImageEquiv 2).symm.trans (bq.trans c)⟩


/-- Every C-component in the normal-X branch centralizes the original section and has an actual Suzuki two-core quotient. -/
theorem quiet_tensor_normal_point_components
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz →
      K ≤ commutatorPreimage d.Gz d.X (d.X.pCoreIn 2) ∧
      ∃ m, 1 ≤ m ∧ Nonempty
        (Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  dsimp only
  intro hnormal K hK
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let B := d.X.subgroupOf d.Gz
  let : B.Normal := hnormal
  let q := QuotientGroup.mk' (pCore 2 d.Gz)
  let E := B.map q
  let : E.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨c⟩ := quiet_tensor_normal_point_residual_image D hn e hbase hzV hz1 hzT hnormal
  let : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  have hE : Nat.card E = 9 := by
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  let J := K.subgroupOf d.Gz
  have hJ : J.IsCComponent := hK.2
  let := hJ.perfect
  constructor
  · apply le_commutatorPreimage hK.1
    have hc := map_mono (f := d.Gz.subtype) (perfect_centralizes_normal_nine_section B hE J)
    rw [map_commutator,map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le (d.X_le.trans inf_le_right)] at hc
    have he : (B.pCoreIn 2).map d.Gz.subtype = d.X.pCoreIn 2 := by
      rw [pCoreIn_subgroupOf 2 d.X d.Gz (d.X_le.trans inf_le_right),
        map_subgroupOf_eq_of_le ((d.X.pCoreIn_le 2).trans (d.X_le.trans inf_le_right))]
    rwa [he] at hc
  · have hz2 : orderOf z = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
    have hsq : IsSQTK KnownSimple.IsKnownSimple d.Gz :=
      D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)
    have hQ : IsSQTK KnownSimple.IsKnownSimple (d.Gz ⧸ pCore 2 d.Gz) := by
      refine ⟨?_,hsq.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hsq.stronglyQuasithin p hp ho)
    let : Group.IsNilpotent (pCore 2 d.Gz) := pCore_isNilpotent
    obtain ⟨m,hm,⟨cJ⟩⟩ := Chapter1.Section02.cComponent_suzuki_of_normal_elementary_nine
      hQ (pCore_quotient_pCore_eq_bot 2) E hE (hJ.map_quotient (pCore 2 d.Gz))
    let k := subgroupOfEquivOfLe hK.1
    let kq := QuotientGroup.congr (pCore 2 J) (pCore 2 K) k (pCore_map_iso 2 k)
    exact ⟨m,hm,⟨kq.symm.trans ((hJ.subnormal.quotientCoreImageEquiv 2).trans cJ)⟩⟩

/-- The normal-X branch supplies an actual Suzuki C-component inside the original section centralizer. -/
theorem quiet_tensor_normal_point_exists_suzuki
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz ∧
      K ≤ commutatorPreimage d.Gz d.X (d.X.pCoreIn 2) ∧
      ∃ m, 1 ≤ m ∧ Nonempty
        (Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  dsimp only
  intro hnormal
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hns : ¬ Group.IsSolvable d.Gz :=
    quiet_tensor_point_centralizer_not_solvable D hn hmany hJ e hbase hzV hz1 hzT
  obtain ⟨J,hJc⟩ := exists_isCComponent_of_not_isSolvable hns
  let K := J.map d.Gz.subtype
  have hK : K ∈ Chapter1.cComponentsIn d.Gz := by
    refine ⟨map_subtype_le _,?_⟩
    change ((J.map d.Gz.subtype).subgroupOf d.Gz).IsCComponent
    have he : (J.map d.Gz.subtype).subgroupOf d.Gz = J :=
      comap_map_eq_self_of_injective d.Gz.subtype_injective J
    rwa [he]
  exact ⟨K,hK,quiet_tensor_normal_point_components D hn e hbase hzV hz1 hzT hnormal K hK⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
