module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ComponentAssembly
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer

/-!
# Connected centralizers of actual toral F4 points

A normalizer point centralizing the toral element fixes its full integral
character evaluation. The checked F4 stabilizer theorem factors its Weyl
image into reflections in vanishing roots. Their actual SL₂ lifts lie in the
centralizer identity component, and the remaining kernel lies in the torus.
Maximal-torus conjugacy inside the centralizer then proves connectedness.

This is the characteristic-two F4 case of Steinberg, *Endomorphisms of Linear
Algebraic Groups*, §3.9(a). It applies to every torus point, including identity,
and introduces no connectedness, class-count, or classification premise.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup

/-- The original closed point centralizer of any point in the actual split
F4 torus is connected in characteristic two. -/
theorem pointCentralizer_isConnected_of_mem_torus (s : PointGroup F)
    (hs : s ∈ F4Chevalley.splitTorus) :
    _root_.IsConnected (pointCentralizer s : Set (PointGroup F)) := by
  let t := (F4Chevalley.splitTorus (k := F)).pointEquiv.symm ⟨s, hs⟩
  have ht : (F4Chevalley.splitTorus (k := F)).includePoint t = s :=
    congrArg Subtype.val ((F4Chevalley.splitTorus (k := F)).pointEquiv.apply_symm_apply _)
  rw [← ht]
  apply SemisimpleCentralizerTori.connected_of_normalizer_le_component
    _ F4Chevalley.splitTorus splitTorus_isMaximal (torus_le_pointCentralizer t)
  intro n hn hN
  exact normalizer_mem_component_of_reflectionKernel t ⟨n, hN⟩
    (F4WeightAction.Stabilizer.mem_reflectionKernel_of_fixed _ _
      (normalizer_centralizer_evaluation_fixed t ⟨n, hN⟩ hn))

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
