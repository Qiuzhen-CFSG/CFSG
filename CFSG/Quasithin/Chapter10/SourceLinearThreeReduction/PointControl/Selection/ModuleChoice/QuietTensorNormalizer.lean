module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCoordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ActionKernel
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SylowStabilizer
public import Theory.Representation.BinaryTensorThree.Normalizer

/-!
# Recovering the outer action from the original tensor base

A tensor identification of the original L₀ image determines the action of
L₀T. Normality puts the whole image in the proved linear normalizer of the
tensor base. The original exchanger has image outside that base: otherwise
it differs from an element of L₀ by an element of the original action
kernel, a normal two-group. Both L₀ and that two-group normalize L,
contradicting the choice of exchanger. Thus the full image is the wreath
group, and the existing Sylow, fixed-point and radical coordinate theorems
apply to the literal S = O₂(XT).

The base-module recognition and the ambient point-core and r > 3 bounds
remain genuine source premises. These conditional weak-closure applications
do not prove either quiet tensor exclusion or FixedSupportRowsAt. Their
assembly remains with the selected-module owner, and final point control
with its existing assembly owner.
Source: Aschbacher--Smith 3.2.6, H.4.4 and 8.3.11--14,
printed pp.581,383--385,726--727.
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

/-- Coordinates only on the original component orbit determine the entire
L₀T tensor image. The original nonnormal exchanger cannot disappear into
the base image, because its action kernel is a two-group normalizing L. -/
theorem quiet_tensor_action_image_of_orbit_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    (quietTensorLinearAction D e).range = BinaryTensorThree.tensorGroup := by
  let H := localJoin T L
  let R := (localOrbit T L).subgroupOf H
  let f := quietTensorLinearAction D e
  have hRH : H ≤ normalizer (localOrbit T L : Set G) :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  let : R.Normal := normal_subgroupOf_of_le_normalizer hRH
  have hbase' : R.map f = BinaryTensorThree.baseAction.range := hbase
  have hnorm : f.range ≤ normalizer
      (BinaryTensorThree.baseAction.range : Set (BinaryTensorThree.Space ≃ₗ[ZMod 2] BinaryTensorThree.Space)) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,hbase'] using R.le_normalizer_map f
  have hKR : IsPGroup 2 f.ker := by
    rw [show f = quietTensorLinearAction D e from rfl,quietTensorLinearAction_ker]
    exact full_module_local_kernel_isTwoGroup D hn
  have hKcore : f.ker ≤ pCore 2 H := le_sSup ⟨inferInstance,hKR⟩
  have hcoreN : H.pCoreIn 2 ≤ normalizer (L : Set G) := by
    have hh := (Chapter1.Section02.local_join_twoCore_le_sylow_stabilizer D.maximal.1).trans
      (show (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (L : Set G) from inf_le_right)
    change (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    rw [componentOrbit_sup]
    exact hh
  have hKN {x : H} (hx : x ∈ f.ker) : (x : G) ∈ normalizer (L : Set G) :=
    hcoreN (mem_map_of_mem H.subtype (hKcore hx))
  apply BinaryTensorThree.eq_tensorGroup_of_base_and_outside f.range
  · rw [←hbase']
    rintro x ⟨a,_,rfl⟩
    exact ⟨a,rfl⟩
  · exact hnorm
  · obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
    let a : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
    refine ⟨f a,⟨a,rfl⟩,?_⟩
    intro hf
    obtain ⟨r,hr,he⟩ := hbase'.ge hf
    have hk : r⁻¹ * a ∈ f.ker := by
      change f (r⁻¹ * a) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hm := (normalizer (L : Set G)).mul_mem
      (source_nonnormal_orbit_le_normalizer D hn hr) (hKN hk)
    apply htn
    change (r : G) * ((r : G)⁻¹ * t) ∈ normalizer (L : Set G) at hm
    simpa only [mul_inv_cancel_left] using hm

/-- The literal weak-closure application with the outer tensor action and
all Sylow, point and radical markings derived from the original L₀ image. -/
theorem quiet_tensor_weakClosure_two_of_orbit_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) :=
  quiet_tensor_weakClosure_two_of_action_image D hJ e
    (quiet_tensor_action_image_of_orbit_image D hn e hbase) hzV hz1 hzT hcore hr

/-- The local-Thompson source consumer now needs only the tensor marking
of L₀, together with the still-open ambient §8.3.11--12 premises. -/
theorem tensor_weakClosure_two_of_local_centralization_three_orbit_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) :=
  quiet_tensor_weakClosure_two_of_orbit_image D hn
    (full_thompson_centralizes_of_local_three D hn hd hJ) e hbase hzV hz1 hzT hcore hr

/-- A surjective tensor marking on L₀ itself supplies the orbit image used
above. It need not specify the action of any exchanger in T. -/
theorem quiet_tensor_orbit_image_of_coordinates
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (q : localOrbit T L →* BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (hq : Function.Surjective q)
    (he : ∀ (a : localOrbit T L) (v : Additive D.fullModule),
      quietTensorLinearAction D e (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) a)
        (e v) = BinaryTensorThree.baseAction (q a) (e v)) :
    ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range := by
  have hact (a : localOrbit T L) :
      quietTensorLinearAction D e (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) a) =
        BinaryTensorThree.baseAction (q a) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    exact he a v
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    let b : localOrbit T L := ⟨a,ha⟩
    exact ⟨q b,(hact b).symm⟩
  · rintro x ⟨g,rfl⟩
    obtain ⟨a,rfl⟩ := hq g
    exact ⟨inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) a,
      a.property,hact a⟩

/-- Original source application from tensor coordinates on L₀ alone,
retaining every original nonidentity T-fixed point. The remaining inputs
are the base-module recognition and the genuine ambient §8.3 bounds. -/
theorem quiet_tensor_weakClosure_two_of_orbit_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (q : localOrbit T L →* BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (hq : Function.Surjective q)
    (he : ∀ (a : localOrbit T L) (v : Additive D.fullModule),
      quietTensorLinearAction D e (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) a)
        (e v) = BinaryTensorThree.baseAction (q a) (e v))
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) :=
  quiet_tensor_weakClosure_two_of_orbit_image D hn hJ e
    (quiet_tensor_orbit_image_of_coordinates D e q hq he) hzV hz1 hzT hcore hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
