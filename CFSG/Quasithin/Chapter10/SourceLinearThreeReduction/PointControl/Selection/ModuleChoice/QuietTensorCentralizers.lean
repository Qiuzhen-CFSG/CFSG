module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorParameters
public import CFSG.Quasithin.Chapter8.Section03.HyperplaneCentralization
public import CFSG.Quasithin.ChapterE.Section03.LocalContainment

/-!
# Initial ambient centralizer bounds for the original tensor radical

The actual tensor-radical hyperplanes and s(G,V)=3 show that W₀(S,V) and
W₁(S,V) centralize V. The original kernel C_T(V) lies in S=O₂(XT), so both
weak closures are computed in that kernel. Its source uniqueness controls
N_G(W₀(S,V)); since V lies in C₁(S,V), its ambient centralizer also lies in M.
This proves the two ambient containments of 8.3.5.

The local E-generation argument then proves 8.3.6 for every overgroup with
the literal S as Sylow and n(H)=1, including every solvable such overgroup.
At n(H)=2 it applies the existing W₂(S,V) theorem, retaining precisely the
point-core and strict-r premises of 8.3.11--12.

Tensor-base recognition and the remaining ambient analysis of 8.3.7--12
still require proofs. The original marking and every prescribed nonidentity
Sylow-fixed point are retained. This does not establish either quiet tensor
exclusion or FixedSupportRowsAt/ModuleChoiceAt. Their discharge remains with
the selected-module owner, and final point control with its existing owner.
Source: Aschbacher--Smith 8.3.3--6 and the end of 8.3.1,
printed pp.723--724,727.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original radical admits no moving corank-zero or corank-one conjugate subgroups. -/
theorem quiet_tensor_weakClosure_low
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) {i : ℕ} (hi : i ≤ 1) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) i ≤
      centralizer (D.fullModule : Set G) := by
  have hs := (quiet_tensor_source_parameters D hn e hbase).2.2
  obtain ⟨q,hq,he⟩ := quiet_exists_tensor_marking_of_action_image D e
    (quiet_tensor_action_image_of_orbit_image D hn e hbase)
  obtain ⟨p,b,hp,hb,hz⟩ := quiet_tensor_marking_at_original_fixed_point D q hq e he
  obtain ⟨r,hr⟩ := quiet_exists_original_radical_coordinates D p hp b hb hzV
    (hz z hzV hz1 hzT) hzT
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hSN : d.S ≤ normalizer (D.fullModule : Set G) := d.S_le_T.trans
    ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
  apply weakClosure_centralizes_of_moving_hyperplanes D.fullModule d.S hSN
    (by rw [hs]; exact_mod_cast (show i+1<3 by omega))
  intro A hA hm
  obtain ⟨B,hBA,hidx,hzB⟩ := tensor_hyperplane_of_radical_coordinates
    D.fullModule d.S hSN r b hr hzV (hz z hzV hz1 hzT) hA.2 hm
  exact ⟨B,hBA,hidx,fun hzero => hz1 (mem_bot.mp (show z ∈ (⊥ : Subgroup G) from hzero ▸ hzB))⟩

/-- C_T(V) lies in the original S=O₂(XT). -/
theorem quiet_kernel_le_point_radical
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) ≤
      CentralizerSetup.S ⟨T,localOrbit T L,z⟩ := by
  let Q := (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXT : d.XT = localJoin T L ⊓ centralizer ({z} : Set G) :=
    quiet_XT_eq_point_centralizer hzT
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
  · rw [hXT]
    exact le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hzV)))
  · exact (hXT.le.trans inf_le_left).trans
      (source_join_normalizes_full_sylow_centralizer D (source_module_nonsolvable_uniqueness D))

/-- The weak closures at indices zero and one are already computed in C_T(V). -/
theorem quiet_tensor_weakClosure_low_eq_kernel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) {i : ℕ} (hi : i ≤ 1) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) i =
      indexedWeakClosure D.fullModule
        ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)) i := by
  apply le_antisymm
  · rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    apply gamma_le_weakClosure
    exact ⟨hA.1,le_inf (hA.2.trans (CentralizerSetup.S_le_T _))
      ((gamma_le_weakClosure hA).trans (quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hi))⟩
  · exact weakClosure_mono _ _ (quiet_kernel_le_point_radical D hzV hzT)

/-- The source equality Wᵢ(S,V)=Wᵢ(Q,V), with the literal Q=O₂(L₀T). -/
theorem quiet_tensor_weakClosure_low_eq_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) {i : ℕ} (hi : i ≤ 1) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) i =
      indexedWeakClosure D.fullModule ((localJoin T L).pCoreIn 2) i := by
  have hk : (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) =
      (localJoin T L).pCoreIn 2 := by
    rw [quiet_tensor_fullModule_eq_module D e hbase]
    exact D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)
  rw [quiet_tensor_weakClosure_low_eq_kernel D hn e hbase hzV hz1 hzT hi,hk]

/-- Both ambient containments of source 8.3.5, on the original subgroup S. -/
theorem quiet_tensor_point_radical_control
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    normalizer (indexedWeakClosure D.fullModule
      (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 0 : Set G) ≤ D.maximalLocal ∧
    centralizer (weakCentralizer D.fullModule
      (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 1 : Set G) ≤ D.maximalLocal := by
  let Q := (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hVQ : D.fullModule ≤ Q :=
    le_inf (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)) (le_centralizer _)
  have hVS := hVQ.trans (quiet_kernel_le_point_radical D hzV hzT)
  have h0 := quiet_tensor_weakClosure_low_eq_kernel D hn e hbase hzV hz1 hzT (i := 0) (by decide)
  constructor
  · rw [h0]
    apply normalizer_le_of_unique_maximalTwoLocal
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
      (T.isPGroup'.to_le ((indexedWeakClosure_le _ _ _).trans inf_le_left))
    · intro hzero
      have hV := (self_le_weakClosure_zero hVQ).trans_eq hzero
      exact hz1 (show z = 1 from hV hzV)
    · exact (source_join_normalizes_full_sylow_centralizer D
        (source_module_nonsolvable_uniqueness D)).trans
        (normalizer_le_weakClosure_normalizer D.fullModule Q 0)
  · have hVC : D.fullModule ≤ weakCentralizer D.fullModule d.S 1 :=
      le_inf hVS (le_centralizer_iff.mp (quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT le_rfl))
    exact (centralizer_le hVC).trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)

/-- Source 8.3.6 for the literal point-radical Sylow subgroup, without a local classification callback. -/
theorem quiet_tensor_generation_one_overgroup_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hS : Chapter1.IsSylowIn 2
      (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) H)
    (hgen : generationParameter H = 1) : H ≤ D.maximalLocal := by
  obtain ⟨P,hP⟩ := hS
  have hg : IsEGeneratedAt 1 P := by
    have hh := isEGenerated_generationParameter_of_pos (G := H) (by omega) P
    rwa [hgen] at hh
  apply LocalContainment.le_of_isEGenerated (V := D.fullModule) P hg
  · rw [hP]
    exact (CentralizerSetup.S_le_T _).trans
      ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
  · rw [hP]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hP]
    exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide

/-- Every solvable overgroup with the original point radical as Sylow lies in M. -/
theorem quiet_tensor_solvable_overgroup_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (H : Subgroup G) [Group.IsSolvable H] (hS : Chapter1.IsSylowIn 2
      (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) H) : H ≤ D.maximalLocal := by
  obtain ⟨P,hP⟩ := hS
  apply LocalContainment.le_of_isEGenerated (V := D.fullModule) P (isEGenerated_one_of_solvable P)
  · rw [hP]
    exact (CentralizerSetup.S_le_T _).trans
      ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
  · rw [hP]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hP]
    exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide

/-- The generation-two endpoint in the proof of 8.3.1. The remaining ambient
analysis must supply the point-core inclusion, r>3, and the escaping overgroup. -/
theorem quiet_tensor_generation_two_overgroup_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule)
    (H : Subgroup G) (hS : Chapter1.IsSylowIn 2
      (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) H)
    (hgen : generationParameter H = 2) : H ≤ D.maximalLocal := by
  obtain ⟨P,hP⟩ := hS
  have hg : IsEGeneratedAt 2 P := by
    have hh := isEGenerated_generationParameter_of_pos (G := H) (by omega) P
    rwa [hgen] at hh
  apply LocalContainment.le_of_isEGenerated (V := D.fullModule) P hg
  · rw [hP]
    exact (CentralizerSetup.S_le_T _).trans
      ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
  · rw [hP]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hP]
    by_cases hj1 : j ≤ 1
    · exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj1
    · have hj2 : j = 2 := by omega
      subst j
      exact (quiet_tensor_source_weakClosure_two D hn hJ e hbase hzV hz1 hzT hcore hr).2
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
