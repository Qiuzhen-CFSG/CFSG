module
public import Theory.Representation.PSL3Two.NaturalDualSections
public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# The six-dimensional binary linear modules are not FF modules

The line core has a natural submodule and a dual quotient, whose combined
fixed codimensions exceed every elementary actor's rank. The same argument
applies to the split sum. Graph duality transfers the obstruction to the
point core. These are precisely the module branches used for Thompson
normality in the original linear amalgam.
Source: Aschbacher–Smith B.5.1 and 13.4.7, printed pp.100,900–901.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.FanoNonFF
open FanoDecomposition

/-- The line core exceeds every offender budget. -/
theorem line_not_ff : ¬ IsFFModule lineCoreRepresentation :=
  NaturalDualSections.not_ff lineCoreRepresentation lineEvaluation lineEvaluation_injective
    lineWeightedSum lineWeightedSum_surjective

/-- Coordinate duality gives the same obstruction for the point core. -/
theorem point_not_ff : ¬ IsFFModule U₂ := by
  intro h
  apply line_not_ff
  apply h.map_equivariant U₂ lineCoreRepresentation AutomorphismAction.graph.toMonoidHom
    AutomorphismAction.graph.injective coreDuality
  intro g v
  have he := LinearMap.congr_fun (coreDualityEquiv.isIntertwining' (AutomorphismAction.graph g)) v
  change coreDuality (U₂ (AutomorphismAction.graph (AutomorphismAction.graph g)) v) =
    lineCoreRepresentation (AutomorphismAction.graph g) (coreDuality v) at he
  rwa [AutomorphismAction.graph_graph] at he

/-- The oppositely oriented natural sum is not an FF module. -/
theorem sum_not_ff : ¬ IsFFModule (W.prod W.dual) := by
  let i : W.IntertwiningMap (W.prod W.dual) := {
    toLinearMap := LinearMap.inl (ZMod 2) Vector (Module.Dual (ZMod 2) Vector)
    isIntertwining' g := by ext v <;> simp }
  let q : (W.prod W.dual).IntertwiningMap W.dual := {
    toLinearMap := LinearMap.snd (ZMod 2) Vector (Module.Dual (ZMod 2) Vector)
    isIntertwining' g := by ext v <;> rfl }
  exact NaturalDualSections.not_ff _ i (fun _ _ h => congrArg Prod.fst h)
    q (fun v => ⟨(0,v),rfl⟩)
end BinaryLinearThree.FanoNonFF

