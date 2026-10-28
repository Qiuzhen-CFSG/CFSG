module
public import Theory.Representation.PSL3Two.FanoCoreStructure
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.DualCore
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# A fixed displacement in the binary Fano core

The dual-natural socle contains a nonzero vector fixed by the embedded
two-residual of the line parabolic. The same vector is the displacement
of a marked transvection on another vector. Evaluation embeds both
vectors into the actual six-dimensional point core.

This fixed displacement supplies the central seed in the faithful branch
of Aschbacher–Smith 14.7.25, printed pp.1051–1052, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Matrix
namespace BinaryLinearThree
open FanoCoreStructure FanoDecomposition ParabolicCyclic.ChiefCounts AutomorphismAction

private theorem axis_fixed (g : actor) :
    W (graph g.val) (![0,0,1] : Vector) = ![0,0,1] := by
  have hp := actor_le_lineParabolic (actor.inv_mem g.property)
  obtain ⟨h20,h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g.val⁻¹).mp hp
  have h22 := naturalPlane_central_top g⁻¹ (Pi.single 2 1 : Vector) Submodule.mem_top
  change (g.val⁻¹.val *ᵥ (Pi.single 2 1 : Vector)) 2 - (Pi.single 2 1 : Vector) 2 = 0 at h22
  rw [mulVec_single_one] at h22
  simp only [col_apply,Pi.single_eq_same] at h22
  have h22' : g.val⁻¹.val 2 2 = 1 := sub_eq_zero.mp h22
  change (g.val⁻¹.val)ᵀ *ᵥ (![0,0,1] : Vector) = _
  ext i
  simp only [mulVec,dotProduct,Fin.sum_univ_three,transpose_apply]
  change g.val⁻¹.val 0 i * 0 + g.val⁻¹.val 1 i * 0 + g.val⁻¹.val 2 i * 1 = (![0,0,1] : Vector) i
  simp only [mul_zero,zero_add,mul_one]
  fin_cases i
  · exact h20
  · exact h21
  · exact h22'

private theorem upper_actor : Matrix.PSL3Two.Bruhat.upper 2 ∈ actor := by
  rw [actor_eq_lineA]
  decide +kernel

private theorem axis_moved :
    W (graph (Matrix.PSL3Two.Bruhat.upper 2)) (![1,0,0] : Vector) - ![1,0,0] = ![0,0,1] := by
  decide +kernel

/-- The core has a nonzero residual-fixed vector that is also a displacement
of the same residual. Both properties use the literal line-parabolic actor. -/
theorem core_exists_fixed_displacement :
    ∃ (v w : Core) (a : actor), v ≠ 0 ∧ (∀ g : actor, U₂ g.val v = v) ∧
      U₂ a.val w - w = v := by
  let f : Representation.IntertwiningMap (W.comp graph.toMonoidHom) U₂ :=
    pointEvaluation.comp graphNaturalDual.toIntertwiningMap
  let v : Core := f (![0,0,1] : Vector)
  let w : Core := f (![1,0,0] : Vector)
  have hf : Function.Injective f := pointEvaluation_injective.comp graphNaturalDual.injective
  refine ⟨v,w,⟨Matrix.PSL3Two.Bruhat.upper 2,upper_actor⟩,?_,?_,?_⟩
  · intro hv
    have he : (![0,0,1] : Vector) = 0 := hf (hv.trans f.map_zero.symm)
    exact one_ne_zero (congrFun he 2)
  · intro g
    change U₂ g.val (f _) = f _
    rw [←IntertwiningMap.isIntertwining]
    exact congrArg f (axis_fixed g)
  · change U₂ _ (f _) - f _ = f _
    rw [←IntertwiningMap.isIntertwining,←map_sub]
    exact congrArg f axis_moved

end BinaryLinearThree
