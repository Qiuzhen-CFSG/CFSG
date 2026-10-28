module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalInput
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.Comparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinAction

/-!
# Transport of the concrete D4 natural highest vector

A compatible regular map to Clifford Spin pulls back its eight-dimensional
rational action. The concrete highest vector is fixed by every actual positive
root subgroup, and the first raw torus coordinate acts inversely. Thus its
character is exactly `E_left(Pi.single 0 1) = E_raw(-Pi.single 0 1)`.

The concrete action and all transport steps are proved here. Unconditional
existence for arbitrary Geometry still requires constructing SpinComparison;
no classification or highest-weight existence placeholder supplies that map.

Sources: GLS3 Example 1.14.9(d), `refs/KGroup/GLS3/Chapter1.tex`;
Steinberg (6.1) and §13, `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open D4RestrictedWeight
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

open NaturalConstruction

/-- Pull back the concrete rational action along a compatible algebraic map. -/
def naturalModule_of_spinComparison (S : Geometry K) (C : SpinComparison k S) :
    NaturalModule S where
  action := ⟨(coordinateAction k).action.comp C.morphism.onPoints⟩
  rational := by
    obtain ⟨b, f, hf⟩ := coordinateAction_rational k
    exact ⟨b, f.comp C.morphism, fun g => hf (C.morphism.onPoints g)⟩
  vector := coordinateVector k
  vector_ne_zero := coordinateVector_ne_zero k
  torus := by
    intro t
    change ((coordinateAction k).action (C.morphism.onPoints (S.torus.includePoint t))).1 _ = _
    rw [C.torus, coordinateVector_parameter, S.leftWeightEmbedding_eq_inv,
      LeftWeights.pointCharacter_inv]
    rfl
  positive_root := by
    intro r hr z
    obtain ⟨a, ha⟩ := C.positive_root r hr z
    change ((coordinateAction k).action
      (C.morphism.onPoints ((S.roots.rootSubgroup r).includePoint z))).1 _ = _
    rw [ha]
    exact coordinateVector_root k (S.rootIndex r) ((S.positive r).mp hr) a

/-- The compatible geometric comparison suffices for the requested natural module.
This conditional result does not assert existence of the comparison. -/
theorem nonempty_naturalModule_of_spinComparison (S : Geometry K)
    (h : Nonempty (SpinComparison k S)) : Nonempty (NaturalModule S) := by
  obtain ⟨C⟩ := h
  exact ⟨naturalModule_of_spinComparison k S C⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
