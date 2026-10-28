module
public import Theory.SpecificGroups.SymmetricFourWreath.OrthogonalB

/-!
# Marked orthogonal actors and the two dihedral four-planes

The full plus isometry group is transitive on its six nonsingular vectors.
A cubic actor on the second plane fixes the first and its square minus the
identity maps onto the second plane. The coordinate formulas retain t and
the actual second wreath factor. Odd products in the normal four-plane and
the product of the two four-planes complete the residual-generation inputs.

Source: Aschbacher–Smith 13.9.5, printed p.971 (PDF p.988).
-/

@[expose] public section
namespace SymmetricFourWreath.OrthogonalB
open BinaryFourPlus
open scoped IsMulCommutative
private instance : DecidableEq W := (RegularWreathProduct.equivProd S4 SymmetricFourWreath.C2).injective.decidableEq

theorem nonsingular_transitive (u v:V) (hu:q u=1) (hv:q v=1) :
    ∃g:q.isometrySubgroup,g.val u=v := by
  obtain ⟨p,hp⟩ := nonsingularEquiv.surjective ⟨u,hu⟩
  obtain ⟨r,hr⟩ := nonsingularEquiv.surjective ⟨v,hv⟩
  have hp' : nonsingularVector p=u := congrArg Subtype.val hp
  have hr' : nonsingularVector r=v := congrArg Subtype.val hr
  let w:Wreath := ⟨fun _=>Equiv.swap p.1 r.1,r.2*p.2⁻¹⟩
  refine ⟨wreathToIsometry w,?_⟩
  rw [←hp',←hr',wreathToIsometry_nonsingular]
  congr 1
  apply Prod.ext
  · exact Equiv.swap_apply_left _ _
  · exact inv_mul_cancel_right r.2 p.2

def cubicPermutation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

def secondCubicWord : Wreath := ⟨fun i=>if i=1 then 1 else cubicPermutation,1⟩

theorem secondCubicWord_cube : secondCubicWord^3=1 := by
  apply RegularWreathProduct.ext
  · funext i
    revert i
    decide +kernel
  · decide +kernel

theorem secondCubicWord_fix_first (u:Plane) :
    (wreathToIsometry secondCubicWord).val (u,0)=(u,0) := by
  rw [wreathToIsometry_apply]
  simp [secondCubicWord]

theorem t_coordinate : ((linearCoordinates.symm (nonzeroVector 2,0)).toMul:W)=t := by
  rw [linearCoordinates_symm_apply]
  decide +kernel

theorem second_coordinate (u:Plane) :
    ((linearCoordinates.symm (0,u)).toMul:W)=factor SymmetricFourWreath.turn (square (planeWord u)) := by
  rw [linearCoordinates_symm_apply]
  revert u
  decide +kernel

private theorem cubic_difference : ∀i:Fin 3,∃j:Fin 3,
    nonzeroVector ((cubicPermutation^2) j)-nonzeroVector j=nonzeroVector i := by decide +kernel

theorem secondCubicWord_difference (u:Plane) : ∃v:Plane,
    (wreathToIsometry (secondCubicWord^2)).val (0,v)-(0,v)=(0,u) := by
  by_cases hu:u=0
  · subst u
    refine ⟨0,?_⟩
    change (wreathToIsometry (secondCubicWord^2)).val (0:V)-0=0
    rw [map_zero,sub_zero]
  obtain ⟨i,hi'⟩ := (by decide +kernel : ∀u:Plane,u≠0→∃i:Fin 3,nonzeroVector i=u) u hu
  obtain ⟨j,hj⟩ := cubic_difference i
  refine ⟨nonzeroVector j,?_⟩
  have hr : (secondCubicWord^2).right=1 := by decide +kernel
  have hl : (secondCubicWord^2).left swapIndex=cubicPermutation^2 := by decide +kernel
  rw [wreathToIsometry_apply,if_pos hr]
  simp only [map_zero,hl,planeLinear_nonzeroVector,Prod.mk_sub_mk,sub_self]
  exact congrArg (fun w:Plane=>(0,w)) (hj.trans hi')

theorem normal_plane_odd_products : ∀a:plane true,∃b:S4,
    b^3=1 ∧ (b⁻¹*square a)^3=1 := by decide +kernel

theorem dihedral_two_planes : ∀a:D8,∃b:plane true,∃c:plane false,a=(b:D8)*(c:D8) := by
  decide +kernel

theorem base_class_axes : ∀a b:D8,
    (InvolutionClasses.classIndex (sylowEmbedding (pair (a,b)))=1 ∨
     InvolutionClasses.classIndex (sylowEmbedding (pair (a,b)))=2) ↔ a=1 ∨ b=1 := by
  decide +kernel

theorem base_class_not_swap : ∀a b:D8,
    InvolutionClasses.classIndex (sylowEmbedding (pair (a,b)))≠5 := by decide +kernel
end SymmetricFourWreath.OrthogonalB
