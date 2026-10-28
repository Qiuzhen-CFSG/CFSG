module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorNonFF
public import Theory.Representation.BinaryTensorThree.SylowMarking

/-!
# Marking the original quiet tensor action at its Sylow subgroup

An equivariant tensor action on the original Sylow subgroup descends through
its literal induced automizer. Faithfulness identifies the kernel, without
assuming that the map to the tensor group is injective. Conjugating its image
into the concrete tensor Sylow transports the module coordinates at the same
time. This constructs the small-model marking previously required by the
non-FF and fusion consumers.

The source must still recognize the original action as the tensor row.
The point-core inclusion and strict global-r bound are the ambient conclusions
8.3.11--12, and remain explicit in the weak-closure application. The radical
coordinates preserve the original point independently of the Sylow marking.
No fixed-support or tensor-exclusion conclusion is asserted here.

Source: Aschbacher--Smith H.4.8(4), 3.2.10(6b), and 8.3.13--14,
printed pp.383,583--584,727.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Construct the exact Sylow-automizer coordinates from the original
conjugation action, allowing its original centralizer kernel. -/
theorem quiet_exists_tensor_sylow_coordinates
    (q : T →* BinaryTensorThree.Group)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (s : T) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨s,D.maximalLocal_normalizes_fullModule
            (le_normalizer_componentOrbit L T s.property)⟩ v.toMul)) =
        BinaryTensorThree.action (q s) (e v)) :
    ∃ (f : inducedAutomizer D.fullModule (T : Subgroup G) →* BinaryTensorThree.Small.P)
      (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space),
      ∀ a v, b (automizerRepresentation D.fullModule a.val v) =
        BinaryTensorThree.Small.actionSmall (f a) (b v) := by
  let V := D.fullModule
  let N := normalizer (V : Set G)
  let A := inducedAutomizer V (T : Subgroup G)
  let ρ := (automizerRepresentation V).comp A.subtype
  have hTN : (T : Subgroup G) ≤ N :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  let π : T →* A :=
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hTN)).codRestrict _
      (fun s => ⟨⟨s,hTN s.property⟩,s.property,rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨a,⟨n,hn,rfl⟩⟩
    exact ⟨⟨n,hn⟩,rfl⟩
  have hρ : Function.Injective ρ :=
    (automizerRepresentation_injective V).comp A.subtype_injective
  obtain ⟨f,_,hf,_⟩ := faithful_action_factor ρ BinaryTensorThree.action hρ
    BinaryTensorThree.action_faithful π hπ q e he
  exact BinaryTensorThree.exists_twoGroup_coordinates ρ
    (T.isPGroup'.of_surjective π hπ) f e hf

/-- Non-FF on the full ambient automizer, using a marking of the original
Sylow action rather than an assumed small-model automizer map. -/
theorem quiet_automizer_notFF_of_original_tensor_action
    (q : T →* BinaryTensorThree.Group)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (s : T) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨s,D.maximalLocal_normalizes_fullModule
            (le_normalizer_componentOrbit L T s.property)⟩ v.toMul)) =
        BinaryTensorThree.action (q s) (e v)) :
    ¬ IsFFModule (automizerRepresentation D.fullModule) := by
  obtain ⟨f,b,hb⟩ := quiet_exists_tensor_sylow_coordinates D q e he
  exact quiet_automizer_notFF_of_tensor_sylow D f b hb

/-- The original S = O₂(XT) application with its Sylow marking constructed
from the actual tensor action. The ambient centralizer premises remain. -/
theorem quiet_original_tensor_weakClosure_two_of_original_action
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (qT : T →* BinaryTensorThree.Group)
    (eT : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (heT : ∀ (s : T) (v : Additive D.fullModule),
      eT (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨s,D.maximalLocal_normalizes_fullModule
            (le_normalizer_componentOrbit L T s.property)⟩ v.toMul)) =
        BinaryTensorThree.action (qT s) (eT v))
    {z : G} (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    let S := CentralizerSetup.S ⟨T,localOrbit T L,z⟩
    let hSN : S ≤ normalizer (D.fullModule : Set G) :=
      (CentralizerSetup.S_le_T ⟨T,localOrbit T L,z⟩).trans
        ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
    ∀ (q : S →* BinaryTensorThree.Radical × BinaryTensorThree.Radical)
      (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space),
      (∀ (s : S) (v : Additive D.fullModule),
        e (Additive.ofMul
          (D.fullModule.normalizerMonoidHom ⟨s,hSN s.property⟩ v.toMul)) =
          BinaryTensorThree.action (BinaryTensorThree.radicalPair (q s)) (e v)) →
      e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point →
      indexedWeakClosure D.fullModule S 2 ≤ centralizer (D.fullModule : Set G) := by
  obtain ⟨f,b,hb⟩ := quiet_exists_tensor_sylow_coordinates D qT eT heT
  exact quiet_original_tensor_weakClosure_two_of_sylow_and_radical_coordinates
    D hJ f b hb hzV hcore hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
