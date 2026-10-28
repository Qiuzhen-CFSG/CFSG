module
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourEndpointInclusions

/-! The existing endpoint duality restricts to the entire literal Borel and
exchanges its ordered root planes, including the full cubic torus. -/
public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural

private theorem duality_unipotent (u : U F) :
    endpointDuality (pointUnipotent u)=lineUnipotent ⟨u.y,u.x,u.x*u.y+u.c⟩ := by
  apply (lineLocalProjectEquiv F).symm.injective
  simp only [endpointDuality,pointUnipotent,lineUnipotent,MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change flagDuality F (specialLinear F u)=specialLinear F _
  apply Subtype.ext
  change (specialLinear F u)⁻¹.val.transpose.submatrix Fin.rev Fin.rev=matrix F _
  rw [←(specialLinear F).map_inv u]
  change (matrix F u⁻¹).transpose.submatrix Fin.rev Fin.rev=matrix F _
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Inv.inv,CharTwo.neg_eq,sub_eq_add_neg]

private theorem duality_borel_mem (b : borel F) :
    (endpointDuality (pointBorelInclusion b) : PSL(3,F))∈borel F := by
  obtain ⟨u,t,rfl⟩ := borel_four_factorization b
  have hu : pointBorelInclusion (borelUnipotent F u)=pointUnipotent u := rfl
  have ht : pointBorelInclusion (simultaneousTorus F t)=pointTorus t :=
    Subtype.ext (pointTorus_val t).symm
  rw [map_mul,map_mul,hu,ht,duality_unipotent]
  change projective F _ * (endpointDuality (pointTorus t) : PSL(3,F))∈borel F
  rw [show endpointDuality (pointTorus t)=lineTorus t from endpointDuality.apply_symm_apply _,
    lineTorus_val]
  exact (borel F).mul_mem (borelUnipotent F _).property (simultaneousTorus F t).property

/-- The actual duality restricts to the full Borel, with its exact unipotent
coordinates. In particular it exchanges the original two root planes. -/
theorem exists_borel_endpoint_duality :
    ∃ d : MulAut (borel F),
      (∀ b,endpointDuality (pointBorelInclusion b)=lineBorelInclusion (d b)) ∧
      (∀ u : U F,d (borelUnipotent F u)=borelUnipotent F ⟨u.y,u.x,u.x*u.y+u.c⟩) := by
  let f : borel F →* borel F := {
    toFun := fun b => ⟨endpointDuality (pointBorelInclusion b),duality_borel_mem b⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun a b => Subtype.ext (by simp) }
  have hf : Function.Injective f := by
    intro a b he
    apply (inclusion_injective borel_four_le_pointLocal)
    apply endpointDuality.injective
    apply Subtype.ext
    change (f a : PSL(3,F))=(f b : PSL(3,F))
    exact congrArg Subtype.val he
  let d := MulEquiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  refine ⟨d,fun _ => rfl,fun u => ?_⟩
  apply Subtype.ext
  change (endpointDuality (pointUnipotent u) : PSL(3,F))=projective F _
  rw [duality_unipotent,lineUnipotent_val]

end Matrix.PSL3.SmallCompletion
