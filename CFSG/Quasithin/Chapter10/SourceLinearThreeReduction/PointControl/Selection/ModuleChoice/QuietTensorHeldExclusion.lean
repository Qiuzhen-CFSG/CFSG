module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorZero
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorBinaryExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Held

/-!
# Excluding the retained Held point-centralizer component

The literal K_z T has E-generation parameter at most one in the Held row.
This follows from the already proved Held local-pair generation theorem,
transported through the original C-component and its exact two-core quotient.
The constructed plane-radical fixed space supplies C_G(C₁(T,V)) ≤ M, while
tensor rigidity supplies N_G(W₀(T,V)) ≤ M. E.3.19 therefore puts K_z T in M,
contradicting the proved escape of K_z. No H-star membership of K_z T is
assumed. The Source consumer removes Held from the actual component sieve.

Tensor recognition, the remaining source geometry, both quiet exclusions,
and the distinct positive-fixed-layer selection still require proofs.
Source: Aschbacher--Smith 8.3.7--10, printed pp.724--726, retaining the Held
row of the corrected intrinsic 1.3.4 catalogue; E.1.14 and E.3.19.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1
open BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The actual invariant Held component and full original Sylow generate
an E-generated-at-one subgroup, with its two-core kernel retained. -/
theorem quiet_tensor_held_join_generation
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hK : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      d.Kz ∈ cComponentsIn d.Gz)
    (hq : IsQuasisimple (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩)))
    (c : XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) ≃* Held.He) :
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
  have hqK : IsQuasisimple (K ⧸ pCore 2 K) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv b.symm
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    change d.Kz.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [← subgroupOf_sup (show d.Kz ≤ Y from le_sup_left)
      (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  have hnK : K.Normal := normal_subgroupOf_of_le_normalizer
    (hYC.trans (le_normalizer_conjugateSpanBy _ _))
  exact SourceLinearThreeReplacement.Overgroups.ModelGeneration.invariantHeldGeneration
    Y hY S K hcomp hnK hqK hKS ⟨b.trans c⟩

/-- The Held alternative contradicts the original tensor weak-centralizer
bounds and the escape of the original component normal closure. -/
theorem quiet_tensor_point_held_excluded
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
    (hq : IsQuasisimple (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩))) :
    ¬ Nonempty (XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) ≃* Held.He) := by
  rintro ⟨c⟩
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let S := T.subtype (show (T : Subgroup G) ≤ d.KzT from le_sup_right)
  have hgen := quiet_tensor_held_join_generation D hzV hz1 hzT hK hq c
  obtain ⟨q,b,hqsurj,hker,hT,hb,hR,hzU,hTU,hthree⟩ :=
    quiet_tensor_plane_fixed_geometry D hn e hbase hzV hz1 hzT
  have hC := quiet_tensor_held_centralizer_le D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P c _ hzU hTU hthree
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
