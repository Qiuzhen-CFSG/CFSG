module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Generation by the residual of a natural point stabilizer

The two-residual of a nonzero-point stabilizer generates the entire binary
three-space by displacements. Transport the marked point calculation along
an actual determinant-one matrix sending the first basis vector to the given
point. Thus the statement retains the literal natural action.

Source: Aschbacher--Smith 10.1.1(3) and the natural-module supplement in the
proof of 10.2.11(3), printed pp.741,754.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag

/-- Every subgroup containing all point-residual displacements is the full natural module. -/
theorem point_residual_movement (v : Model) (hv : v ≠ 1) (D : Subgroup Model)
    (hD : ∀ w : Model, ∀ g ∈ residual (MulAction.stabilizer SL v.toAdd),
      w * (slAut g w)⁻¹ ∈ D) : D = ⊤ := by
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    flagPoint.val v.toAdd flagPoint.property hv
  have hp : MulAction.stabilizer SL v.toAdd =
      pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
    change g • flagPoint.val = v.toAdd at hg
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    congr 1
    rw [← Fano.stabilizer_flagPoint_SL]
    ext x
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hr : residual (MulAction.stabilizer SL v.toAdd) =
      pointA.map (MulAut.conj g).toMonoidHom := by
    have h := map_embedded_pResidual 2 pointParabolicSL (MulAut.conj g).toMonoidHom
    change (residual pointParabolicSL).map (MulAut.conj g).toMonoidHom =
      residual (pointParabolicSL.map (MulAut.conj g).toMonoidHom) at h
    rw [point_residual] at h
    exact hp ▸ h.symm
  have htop : D.comap (slAut g).toMonoidHom = ⊤ := by
    apply plane_movement
    intro w _ a ha
    have h := hD (slAut g w) (g*a*g⁻¹)
      (hr ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    change slAut g (w * (slAut a w)⁻¹) ∈ D
    convert h using 1
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
  apply top_unique
  intro w _
  obtain ⟨u,rfl⟩ := (slAut g).surjective w
  exact show u ∈ D.comap (slAut g).toMonoidHom from htop ▸ mem_top u

end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
