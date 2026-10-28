module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorSuzukiPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietBinaryThreeGeneration
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
public import CFSG.Quasithin.ChapterE.Section03.NormalSectionContainment
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Models
public import Theory.GroupTheory.CComponent.FullSylowJoin

/-!
# Suzuki containment in the original tensor section centralizer

Every escaping Suzuki component gives the actual H-star K join T. That
join has order prime to three, including exchanged components and the
original two-core extension. If its generation parameter exceeds one,
Hall faithfulness and the binary-three overlap force its odd Hall subgroup
to be a three-group, contradicting its nontrivial Cartan torus. At parameter
one, restrict the E-family to the literal normal section centralizer; its
Sylow intersection is the original S, whose low weak closures are already
controlled. Thus the entire H-star, and hence K, lies in M.

The normal-X branch supplies all component markings and section placements.
No equality of generation parameters through the two-core is used. Full
section-centralizer containment, factorization, tensor recognition and the
remaining quiet fixed-support obligations stay with the selected-module
owner; final point control stays with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 8.3.6--7, printed pp.724--725,
using the actual Hall action of 10.2.3(ii), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A three-free H-star in the quiet binary-three row has parameter at most
one. Faithfulness is used only on its actual odd overlap Hall subgroup. -/
theorem quiet_binaryThree_three_free_hstar_generation_le_one
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hfree : ¬ 3 ∣ Nat.card H) :
    generationParameter H ≤ 1 := by
  by_cases hlarge : 1 < generationParameter H
  · have hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
      rintro ⟨a⟩
      have hc := Nat.card_congr (cL.symm.trans a).toEquiv
      rw [Matrix.PSL3Two.card_SL,nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc
    obtain ⟨hP,f,_,hf,d,he,hperm,_⟩ :=
      source_hstar_cartan_data_of_generation_gt_one D hH hlarge
    have hBM := he ▸ d.hall_le
    have hHall := he ▸ d.hall
    have hfaith := source_nonnormalHallFaithful hmany L D hmin hn hna H hH hlarge
      d.witness.abelianGroup hBM hHall d.witness.abelian hperm
    have hcentral : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (quiet_hstar_centralizes_omega D hJ hH)
    let c : CentralHall.Context D H d.witness.abelianGroup :=
      ⟨hmany,hmin,hn,hna,hH,hlarge,hcentral,hBM,hHall,d.witness.abelian,hperm,hfaith⟩
    have hthree : IsPGroup 3 d.witness.abelianGroup :=
      CentralHall.isThreeGroup_of_image D _ hBM hfaith
        (CentralHall.LinearThree.source_image_isThreeGroup D c cL)
    have hBfree : ¬ 3 ∣ Nat.card d.witness.abelianGroup :=
      fun hd => hfree (hd.trans (card_subgroup_dvd_card _))
    obtain ⟨k,hk⟩ := hthree.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hBfree (hk ▸ dvd_pow_self 3 hk0)
    have hBcard : Nat.card d.witness.abelianGroup = 1 := by rw [hk,hk0,pow_zero]
    have hcyc : Nat.card d.witness.cyclicGroup ≤ 1 := by
      rw [←hBcard]
      exact Nat.card_le_card_of_injective (inclusion d.witness.cyclic_le)
        (inclusion_injective _)
    rw [d.witness.card] at hcyc
    have hpow : 4 ≤ 2^f := (by decide : 4 ≤ 2^2).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  · omega

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice

public noncomputable section
open scoped IsMulCommutative Pointwise
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem suzuki_component_join_three_free
    {U K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn U)
    (hTU : (T : Subgroup G) ≤ U) {m : ℕ} (hm : 1 ≤ m)
    (c : Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ 3 ∣ Nat.card (K ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := K ⊔ (T : Subgroup G)
  let A := K.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hA : A.IsCComponent := hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hTU)
  let a : A ≃* K := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let aq := QuotientGroup.congr (pCore 2 A) (pCore 2 K) a (pCore_map_iso 2 a)
  let cA := aq.trans c
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup (A ⧸ pCore 2 A) := cA.isSimpleGroup
  let : Group.IsPerfect A := hA.perfect
  let : Group.IsPerfect (A ⧸ pCore 2 A) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    Chapter1.RadicalNormalizers.Embedding.Alternatives.quasisimple_of_perfect_simple
  have hfree : ¬ 3 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr cA.toEquiv]
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have h := hA.three_free_join S.isPGroup' hfree
  rw [hgen,Nat.card_congr (topEquiv : (⊤ : Subgroup H) ≃* H).toEquiv] at h
  exact h

/-- Parameter-one overgroups in the original section normalizer lie in M.
The E-family is restricted to that normal section, so the original S suffices. -/
theorem quiet_tensor_section_normalizer_generation_one_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHN : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      H ≤ d.Gz ⊓ normalizer (d.X : Set G))
    (hgen : generationParameter H = 1) : H ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  let P := T.subtype hTH
  have hncore : N ≤ normalizer (d.X.pCoreIn 2 : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_characteristic_image d.X (pCore 2 d.X))
  have hNY : N ≤ normalizer (Y : Set G) :=
    commutatorPreimage_normalized N d.X (d.X.pCoreIn 2) N hncore
      N.le_normalizer inf_le_right hncore
  obtain ⟨_,hSY,hmax⟩ := Chapter1.isSylowIn_iff.mp
    (quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT)
  have hTS : (T : Subgroup G) ⊓ Y = d.S :=
    hmax _ (T.isPGroup'.to_le inf_le_left) (le_inf d.S_le_T hSY) inf_le_right
  have hP : (P : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTH
  have hg : IsEGeneratedAt 1 P := by
    have hh := isEGenerated_generationParameter_of_pos (G := H) (by omega) P
    rwa [hgen] at hh
  apply NormalSectionContainment.le_of_isEGenerated (Y := Y) (V := D.fullModule) P hg
  · exact hHN.trans hNY
  · rw [hP]
    exact (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  · rw [hP,hTS]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hP,hTS]
    exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide

/-- Every actual Suzuki component of the literal section centralizer lies in M,
including components exchanged by T and arbitrary original two-core kernels. -/
theorem quiet_tensor_section_suzuki_le_in
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (U : Subgroup G) (hTU : (T : Subgroup G) ≤ U)
    (hUG : U ≤ centralizer ({z} : Set G))
    (hYU : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2) ≤ U) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn U → K ≤ Y →
      (∃ m, 1 ≤ m ∧ Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) → K ≤ D.maximalLocal := by
  dsimp only
  intro K hK hKY hm
  by_contra hnot
  have hH := quiet_tensor_section_suzuki_hstar_in D hn e hbase hzV hz1 hzT U hTU hUG hYU K hK hKY hm hnot
  obtain ⟨m,hm,⟨c⟩⟩ := hm
  have hfree := suzuki_component_join_three_free hK hTU hm c
  have hle := quiet_binaryThree_three_free_hstar_generation_le_one
    D hmany hmin hn hJ cL hH hfree
  have hpos := source_hstar_generation_positive D hH
  have he : generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) = 1 := by omega
  have hTX : (T : Subgroup G) ≤ normalizer
      ((CentralizerSetup.X ⟨T,localOrbit T L,z⟩) : Set G) := by
    rw [←quiet_point_residual_eq (T := T) (L := L) hzT]
    exact (show (T : Subgroup G) ≤ (CentralizerSetup.XT ⟨T,localOrbit T L,z⟩) from le_sup_right).trans
      (le_normalizer_embedded_pResidual 2 _)
  exact hnot (le_sup_left.trans (quiet_tensor_section_normalizer_generation_one_le
    D hn e hbase hzV hz1 hzT _ le_sup_right
    (sup_le (hKY.trans (commutatorPreimage_le _ _ _)) (le_inf hzT hTX)) he))


/-- Suzuki containment for components of the full original point centralizer. -/
theorem quiet_tensor_section_suzuki_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz → K ≤ Y →
      (∃ m, 1 ≤ m ∧ Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) → K ≤ D.maximalLocal := by
  exact quiet_tensor_section_suzuki_le_in D hmany hmin hn hJ cL e hbase hzV hz1 hzT
    (centralizer ({z} : Set G)) hzT le_rfl
    ((commutatorPreimage_le _ _ _).trans inf_le_left)


/-- All C-components of the normal-X point centralizer lie in M. The actual
Suzuki quotients and section containment come from the preceding source classification. -/
theorem quiet_tensor_normal_point_components_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
      ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz → K ≤ D.maximalLocal := by
  dsimp only
  intro hnormal K hK
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨hKY,hm⟩ := quiet_tensor_normal_point_components D hn e hbase hzV hz1 hzT hnormal K hK
  have hnorm : d.Gz ⊓ normalizer (d.X : Set G) = d.Gz :=
    inf_of_le_left ((normal_subgroupOf_iff_le_normalizer
      (d.X_le.trans inf_le_right)).mp hnormal)
  exact quiet_tensor_section_suzuki_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT
    K hK (by rwa [hnorm]) hm

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
