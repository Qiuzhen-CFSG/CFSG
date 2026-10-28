module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietFusion
public import Theory.GroupAction.BinaryTensorHyperplanes

/-!
# Tensor hyperplanes on the original quiet module

The two marked line-parabolic radicals supply the hyperplane in 8.3.14.
The binary character kernel has index two in the original moving actor,
and its centralizer commutator contains the original marked tensor point.
Thus the source consumer needs neither a separate hyperplane nor a separate
conjugacy witness. Equivariant coordinates also prove that the point is an
involution.

The application keeps the literal S = O₂(XT) from the source centralizer
setup. Its source tensor coordinates, local non-FF condition, point-core
inclusion and strict r bound remain explicit. Constructing these inputs and
excluding both quiet tensor alternatives remain with the selected-module
owner; this module does not assert FixedSupportRowsAt or tensor exclusion.
Source: Aschbacher--Smith, 8.3.12--14, printed pp.726--727.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03

/-- The model calculation gives the exact hyperplane witness on ambient
subgroups, with the same tensor point and the same conjugation action. -/
theorem tensor_hasFusedHyperplane_of_radical_coordinates
    {G : Type*} [Group G] (V S : Subgroup G) [IsElementaryAbelian 2 V]
    (hSN : S ≤ normalizer (V : Set G))
    (q : S →* BinaryTensorThree.Radical × BinaryTensorThree.Radical)
    (e : Additive V ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (s : S) (v : Additive V),
      e (Additive.ofMul (V.normalizerMonoidHom ⟨s,hSN s.property⟩ v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.radicalPair (q s)) (e v))
    {z : G} (hzV : z ∈ V)
    (hez : e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point)
    {A : Subgroup G} (hAS : A ≤ S) (hmove : ¬ A ≤ centralizer (V : Set G)) :
    HasFusedHyperplane V A z := by
  obtain ⟨B,hBA,hi,hz⟩ :=
    tensor_hyperplane_of_radical_coordinates V S hSN q e he hzV hez hAS hmove
  exact ⟨B,hBA,hi,z,hz,IsConj.refl z⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The literal quiet tensor consumer with the hyperplane and point-order
premises discharged by actual equivariant radical coordinates. -/
theorem quiet_original_tensor_weakClosure_two_of_coordinates
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype))
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
  dsimp only
  intro q e he hez
  have hzn : z ≠ 1 := by
    intro hz
    have hz0 : (Additive.ofMul ⟨z,hzV⟩ : Additive D.fullModule) = 0 := by
      apply congrArg Additive.ofMul
      exact Subtype.ext hz
    apply BinaryTensorThree.point_ne_zero
    rw [← hez,hz0,map_zero]
  have hz : orderOf z = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hzn
  apply quiet_original_tensor_weakClosure_two D hJ hnf hz hzV hcore hr
  intro A hA hmove
  exact tensor_hasFusedHyperplane_of_radical_coordinates D.fullModule _ _
    q e he hzV hez hA.2 hmove

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
