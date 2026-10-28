module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Binary
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Diagonal
/-!
# Graph-field fixes the universal PSL₃(4) kernel modulo squares

The actual diagonal action has nontrivial cubic image on the binary kernel
quotient and commutes with graph-field. The graph-field image is involutory,
so the checked binary-plane centralizer calculation makes it trivial. Thus
every original universal-kernel displacement is an actual square.

Source: Aschbacher–Smith I.2.2(3b), printed pp.409–410.
-/

public section
open PerfectCentralCovering Subgroup
namespace Matrix.PSL3Four.CentralCover.GraphFieldKernel
open ExtendedCentralizer.CoverCentralizers.DiagonalCenter
open ExtendedCentralizer.ProjectiveFixer

theorem binaryAction_graphField : binaryAction graphField=1 := by
  obtain ⟨u,z,hz⟩ := exists_moving_diagonal
  have hne : binaryAction (diagonalRepresentative u) ≠ 1 := by
    intro he
    apply hz
    apply (binaryProjection_eq_one_iff_square _).mp
    rw [map_mul,map_inv]
    have hh := binaryAction_apply (diagonalRepresentative u) z
    rw [he,MulAut.one_apply] at hh
    rw [←hh,mul_inv_cancel]
  have h3 : binaryAction (diagonalRepresentative u)^3=1 := by
    change binaryActionHom (diagonalRepresentative u)^3=1
    rw [←map_pow,diagonalRepresentative_cube,map_one]
  have h2 : binaryAction graphField^2=1 := by
    change binaryActionHom graphField^2=1
    rw [←map_pow,graphField_sq,map_one]
  exact binary_involutory_centralizer _ _ h3 hne h2
    ((graphField_commutes_diagonal u).symm.map binaryActionHom).eq

theorem graphField_displacement_is_square (z : Kernel) :
    ∃ w : Kernel, w^2=universalKernelMap graphField z*z⁻¹ := by
  apply (binaryProjection_eq_one_iff_square _).mp
  rw [map_mul,map_inv]
  have hh := binaryAction_apply graphField z
  rw [binaryAction_graphField,MulAut.one_apply] at hh
  rw [←hh,mul_inv_cancel]

theorem universalLift_graphField_sq : universalLift graphField^2=1 := by
  rw [pow_two,←universalLift_mul,←pow_two,graphField_sq]
  exact (universalLift_unique 1 1 (fun _ => rfl)).symm
end Matrix.PSL3Four.CentralCover.GraphFieldKernel
