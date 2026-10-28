module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCentralizers
public import CFSG.Quasithin.ChapterE.Section03.NormalSectionContainment
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The generation-two endpoint for the binary tensor module

The actual point Borel normalizes T intersect K_z, placing that intersection
in S = O₂(XT). Consequently K_z S is normalized by K_z T and its intersection
with T is exactly S. Apply E-generation in this normal section: the original
W₀(S,V) normalizer bound and W₂(S,V) centralization force K_z T into M.

ModuleChoice.Source supplies the Borel, generation and weak-closure inputs
from the original marked tensor action and contradicts its H-star escape.
All groups, weak closures and action kernels remain the original ones.
Source: Aschbacher--Smith, conclusion of Theorem 8.3.1, printed p.727,
using 8.3.5, 8.3.10, 8.3.14 and E.3.19.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original point join lies in M once its Borel and second weak closure
are controlled. The normal-section E-generation theorem uses the original
S without changing the generation parameter through a quotient. -/
theorem quiet_tensor_point_generation_endpoint
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hB : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      d.X ≤ normalizer (((T : Subgroup G) ⊓ d.Kz : Subgroup G) : Set G))
    (hgen : generationParameter (CentralizerSetup.KzT ⟨T,localOrbit T L,z⟩) = 2)
    (hW : indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G)) :
    CentralizerSetup.KzT ⟨T,localOrbit T L,z⟩ ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let Y := d.Kz ⊔ d.S
  have hTK : (T : Subgroup G) ≤ normalizer (d.Kz : Set G) :=
    hzT.trans (le_normalizer_conjugateSpanBy d.X d.Gz)
  have hTi : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ d.Kz : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  have hiS : (T : Subgroup G) ⊓ d.Kz ≤ d.S :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) (sup_le hB hTi)
  have hTS : (T : Subgroup G) ⊓ Y = d.S := by
    apply le_antisymm _ (le_inf d.S_le_T le_sup_right)
    rintro a ⟨haT,haY⟩
    have hp : a ∈ (d.Kz : Set G) * (d.S : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left d.Kz d.S (d.S_le_T.trans hTK)]
      exact haY
    obtain ⟨k,hk,s,hs,hks⟩ := hp
    have hkT : k ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem haT ((T : Subgroup G).inv_mem (d.S_le_T hs))
      rwa [←hks,mul_inv_cancel_right] at hh
    rw [←hks]
    exact d.S.mul_mem (hiS ⟨hkT,hk⟩) hs
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    apply (le_inf hTK ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (show (T : Subgroup G) ≤ d.XT from le_sup_right).trans
      (d.XT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.XT (pCore 2 d.XT)))
  have hHY : d.KzT ≤ normalizer (Y : Set G) :=
    sup_le (le_sup_left.trans Y.le_normalizer) hTY
  let P := T.subtype (show (T : Subgroup G) ≤ d.KzT from le_sup_right)
  have hP : (P : Subgroup d.KzT).map d.KzT.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hg : IsEGeneratedAt 2 P := by
    have hh := isEGenerated_generationParameter_of_pos (G := d.KzT) (by rw [hgen]; decide) P
    rwa [hgen] at hh
  apply NormalSectionContainment.le_of_isEGenerated (Y := Y) (V := D.fullModule) P hg hHY
  · rw [hP]
    exact (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  · rw [hP,hTS]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hP,hTS]
    by_cases hj1 : j ≤ 1
    · exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj1
    · have hj2 : j = 2 := by omega
      exact hj2 ▸ hW
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
