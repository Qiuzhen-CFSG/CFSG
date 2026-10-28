module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourCentralExtensions

/-!
# The opposite endpoint central correction

The exact point/line duality transports the proved line correction to the
actual point endpoint. It supplies the independent second central shear,
with literal projective unipotent and full-torus markings retained.
-/

public noncomputable section
open Subgroup Matrix SemidirectProduct
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural

/-- Existing projective point/line duality, with both carriers retained. -/
@[expose] def endpointDuality : pointLocal F ≃* lineLocal F :=
  (pointLocalProjectEquiv F).symm.trans
    ((pointLineLocalEquiv F).trans (lineLocalProjectEquiv F))

/-- Original unitriangular element in the actual point endpoint. -/
@[expose] def pointUnipotent (u : U F) : pointLocal F :=
  pointLocalProjectEquiv F
    ⟨specialLinear F u,(mem_pointLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩

theorem pointUnipotent_val (u : U F) :
    (pointUnipotent u : PSL(3,F))=projective F u := rfl

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

/-- The independent second shear on the actual point endpoint. -/
@[expose] def pointCentralCorrection (k : F) : MulAut (pointLocal F) :=
  (MulAut.congr endpointDuality.symm) (lineCentralCorrection k)

/-- Exact second central correction, on the original U coordinates. -/
theorem pointCentralCorrection_unipotent (k : F) (u : U F) :
    pointCentralCorrection k (pointUnipotent u)=
      pointUnipotent ⟨u.x,u.y,u.c+k*u.y^2⟩ := by
  apply endpointDuality.injective
  change endpointDuality (endpointDuality.symm
    (lineCentralCorrection k (endpointDuality (pointUnipotent u)))) = _
  rw [MulEquiv.apply_symm_apply,duality_unipotent,lineCentralCorrection_unipotent,
    duality_unipotent]
  congr 1
  apply U.ext
  · rfl
  · rfl
  · change u.x*u.y+u.c+k*u.y^2=u.x*u.y+(u.c+k*u.y^2)
    exact add_assoc _ _ _

/-- The full torus in the point endpoint, via the exact duality. -/
@[expose] def pointTorus (t : Fˣ) : pointLocal F := endpointDuality.symm (lineTorus t)

/-- The duality retains exactly the original projective torus element. -/
theorem pointTorus_val (t : Fˣ) :
    (pointTorus t : PSL(3,F))=(simultaneousTorus F t : PSL(3,F)) := by
  let d : lineLocalSL F :=
    ⟨torusSL F (t^2,1),(mem_lineLocalSL_iff F _).mpr (by simp [torusSL_val])⟩
  have he : pointTorus t=pointLocalProjectEquiv F ((pointLineLocalEquiv F).symm d) := by
    apply endpointDuality.injective
    simp [pointTorus,endpointDuality,lineTorus,d]
  rw [he]
  have hf : flagDuality F (torusSL F (t^2,1))=torusSL F (1,(t^2)⁻¹) := by
    apply Subtype.ext
    change (torusSL F (t^2,1))⁻¹.val.transpose.submatrix Fin.rev Fin.rev=(torusSL F (1,(t^2)⁻¹)).val
    rw [←(torusSL F).map_inv (t^2,1)]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [torusSL_val]
  change projection F (flagDuality F (torusSL F (t^2,1)))=torusMap F (t,t⁻¹)
  rw [hf]
  change torusMap F (1,(t^2)⁻¹)=torusMap F (t,t⁻¹)
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul,BorelQuotient.torusMap_eq_one_iff]
  have ht : t^3=1 := by
    have hh := pow_card_eq_one' (x:=t)
    rw [Nat.card_units,Nat.card_eq_fintype_card,card_field] at hh
    exact hh
  constructor
  · simp [pow_two]
  · simpa using congrArg Inv.inv ht

/-- The point correction fixes every element of the same cubic torus. -/
theorem pointCentralCorrection_torus (k : F) (t : Fˣ) :
    pointCentralCorrection k (pointTorus t)=pointTorus t := by
  apply endpointDuality.injective
  change endpointDuality (endpointDuality.symm
    (lineCentralCorrection k (endpointDuality (endpointDuality.symm (lineTorus t))))) = _
  rw [MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply,lineCentralCorrection_torus]
  exact (endpointDuality.apply_symm_apply _).symm

end Matrix.PSL3.SmallCompletion
