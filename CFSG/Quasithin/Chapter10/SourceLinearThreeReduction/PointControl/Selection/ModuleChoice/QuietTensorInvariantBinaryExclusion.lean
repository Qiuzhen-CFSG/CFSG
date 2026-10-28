module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorZero
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorBinaryExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Binary

public import Theory.SpecificGroups.BinaryLinear.ThreeFreeNormalized

/-!
# The invariant binary linear point-centralizer exclusions

A three-free T-invariant subgroup of G_z acts through a two-group on the
original K_z/O₂(K_z): binary flag geometry controls its inner action and
the outer group has order at most two. Its two-residual lies in the full
action kernel, which normalizes X by residual recovery and hence lies in M.
This controls the ambient centralizer of the constructed tensor fixed space,
and therefore C_G(C₁(T,V)). The actual K_z T is E-generated at one by the
proved binary flag generation theorem. Together with N_G(W₀(T,V)) ≤ M,
E.3.19 forces K_z ≤ M, contradicting its original escape.

The Source consumer eliminates both invariant binary alternatives while
preserving the exact two-core quotient, tensor marking and cubic Sylow.
Source: Aschbacher--Smith 8.3.8--10, printed pp.725--726, using E.1.14
and E.3.19. Tensor recognition and the exchanged prime-model branch remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1
open Chapter15.Section04.LocalSetup.EmbeddingReduction
open BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Three-free T-invariant subgroups of the original point centralizer
lie in M in either invariant binary linear row. -/
theorem quiet_tensor_binary_three_free_le
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
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {n : ℕ} (hdim : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)) n 2)
    (Y : Subgroup G) (hY : Y ≤ centralizer ({z} : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hthree : ¬ 3 ∣ Nat.card Y) : Y ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hKn : d.Gz ≤ normalizer (d.Kz : Set G) := le_normalizer_conjugateSpanBy _ _
  let f : d.Gz →* MulAut (XiQuotient d.Kz) :=
    (pCoreNormalizerAction 2 d.Kz).comp (inclusion hKn)
  have hinner : MulAut.innerSubgroup (XiQuotient d.Kz) ≤ f.range := by
    rintro a ⟨q,rfl⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Kz) q
    exact ⟨⟨k,d.Kz_le_Gz k.property⟩,pCoreNormalizerAction_on_component 2 d.Kz k⟩
  obtain ⟨c⟩ := BinaryAction.binary_linear_equiv (by omega : 0 < n) hm
  have hz : center (XiQuotient d.Kz) = ⊥ :=
    Chapter15.Section04.LocalSetup.binary_linear_center_eq_bot (by omega) hm
  have ho : IsPGroup 2 (MulAut.Outer (XiQuotient d.Kz)) := by
    have hb := BinaryAction.binary_outer_card_le_two hdim hm
    change Nat.card (MulAut.Outer (XiQuotient d.Kz)) ≤ 2 at hb
    have hp : 0 < Nat.card (MulAut.Outer (XiQuotient d.Kz)) := Nat.card_pos
    have hc : Nat.card (MulAut.Outer (XiQuotient d.Kz)) = 1 ∨
        Nat.card (MulAut.Outer (XiQuotient d.Kz)) = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa using hc)
    · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc)
  have hmodel : ∀ (S : Sylow 2 (BinaryLinear.OuterCyclic.LinearGroup n))
      (V : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n)),
      (S : Subgroup _) ≤ normalizer (V : Set (BinaryLinear.OuterCyclic.LinearGroup n)) →
      ¬ 3 ∣ Nat.card V → IsPGroup 2 V := by
    rcases hdim with rfl | rfl
    · exact BinaryLinear.ThreeFreeSylowOvergroups.normalized_three_free_isPGroup
    · exact BinaryLinear.ThreeFreeSylowOvergroups.normalized_three_free_isPGroup
  have hYz : Y ≤ d.Gz := hY
  let R : Sylow 2 d.Gz := T.subtype hzT
  let Y' := Y.subgroupOf d.Gz
  have hnorm : (R : Subgroup d.Gz) ≤ normalizer (Y' : Set d.Gz) := by
    change (T : Subgroup G).subgroupOf d.Gz ≤ normalizer (Y.subgroupOf d.Gz : Set d.Gz)
    rw [←subgroupOf_normalizer_eq hYz]
    exact comap_mono hTY
  have hthree' : ¬ 3 ∣ Nat.card Y' := by
    change ¬ 3 ∣ Nat.card (Y.subgroupOf d.Gz)
    rw [Nat.card_congr (subgroupOfEquivOfLe hYz).toEquiv]
    exact hthree
  have hbound := le_ker_sup_sylow_of_three_free_automorphism_model R f hinner hz ho Y'
    hnorm hthree' c hmodel
  have hcoreH : d.Gz.pCoreIn 2 ≤ normalizer (d.X : Set G) := by
    rw [←hi.residual]
    exact le_sup_left.trans (le_normalizer_embedded_pResidual 2 _)
  have hcore : d.Kz.pCoreIn 2 ≤ normalizer (d.X : Set G) :=
    (pCoreIn_mono_of_normalizes d.Kz_le_Gz hKn).trans hcoreH
  have hker : f.ker.map d.Gz.subtype ≤ D.maximalLocal := by
    rintro g ⟨x,hx,rfl⟩
    apply quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT
    refine ⟨x.property,?_⟩
    apply mem_normalizer_of_pCoreNormalizerAction_preserves_image d.Kz d.X d.X_le_Kz
      hi.perfect hcore (inclusion hKn x)
    change pCoreNormalizerAction 2 d.Kz (inclusion hKn x) = 1 at hx
    rw [hx]
    exact map_id _
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hm := map_mono (f := d.Gz.subtype) hbound
  have hmap : Y'.map d.Gz.subtype = Y := map_subgroupOf_eq_of_le hYz
  rw [hmap,Subgroup.map_sup] at hm
  have hR : (R : Subgroup d.Gz).map d.Gz.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hzT
  rw [hR] at hm
  exact hm.trans (sup_le hker hTM)

/-- Binary flag generation on the original K_z T, transported through
its actual component and two-core. -/
theorem quiet_tensor_binary_join_generation
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hK : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      d.Kz ∈ cComponentsIn d.Gz)
    {n : ℕ} (hdim : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)) n 2) :
    IsEGenerated 1 (CentralizerSetup.KzT ⟨T,localOrbit T L,z⟩) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let Y := d.KzT
  have hYC : Y ≤ d.Gz := sup_le d.Kz_le_Gz hzT
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hY : IsSQTK KnownSimple.IsKnownSimple Y :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hYC)).mp
      ((D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)).subgroup _)
  let K := d.Kz.subgroupOf Y
  let S := T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right)
  have hcomp : K.IsCComponent := hK.2.subgroupOf_of_le le_sup_left hYC
  let a := subgroupOfEquivOfLe (show d.Kz ≤ Y from le_sup_left)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    change d.Kz.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [← subgroupOf_sup (show d.Kz ≤ Y from le_sup_left)
      (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  let hnK : K.Normal := normal_subgroupOf_of_le_normalizer
    (hYC.trans (le_normalizer_conjugateSpanBy _ _))
  exact SourceLinearThreeReplacement.Overgroups.ModelGeneration.isEGenerated_of_normal_binary_component
    hY S K hcomp hKS hdim (hm.of_mulEquiv b)

/-- Both invariant binary linear models contradict the original tensor
weak-centralizer bounds and the escape of K_z. -/
theorem quiet_tensor_point_binary_excluded
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
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (hK : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      d.Kz ∈ cComponentsIn d.Gz)
    {n : ℕ} (hdim : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)) n 2 := by
  intro hm
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let S := T.subtype (show (T : Subgroup G) ≤ d.KzT from le_sup_right)
  have hgen := quiet_tensor_binary_join_generation D hzV hz1 hzT hK hdim hm
  obtain ⟨q,b,hqsurj,hker,hT,hb,hR,hzU,hTU,hthree⟩ :=
    quiet_tensor_plane_fixed_geometry D hn e hbase hzV hz1 hzT
  have hC := quiet_tensor_binary_three_free_le D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P hdim hm (centralizer (originalFixed D.fullModule (localJoin T L) q : Set G))
    (centralizer_le (Set.singleton_subset_iff.mpr hzU))
    (hTU.trans (normalizer_le_normalizer_centralizer _)) hthree
  have hs := (quiet_tensor_source_parameters D hn e hbase).2.2
  have hU := quiet_tensor_plane_fixed_le_weakCentralizer D hs q hqsurj b hT hb
  have hC1 := (centralizer_le hU).trans hC
  have hmap : (S : Subgroup d.KzT).map d.KzT.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hYM : d.KzT ≤ D.maximalLocal := by
    apply WeakCentralizerContainment.le_of_isEGenerated_one (V := D.fullModule) S (hgen S)
    · rw [hmap]
      exact quiet_tensor_weakClosure_zero_normalizer D hs q b hT hb
    · rw [hmap]
      exact inf_le_right.trans hC1
    · rw [hs]
      decide
  exact quiet_tensor_point_normalClosure_not_le D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P (le_sup_left.trans hYM)


end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
