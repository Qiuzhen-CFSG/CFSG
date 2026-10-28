module
public import Theory.Representation.HermitianTensorThree.PointSection.Transvections
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Contracts

/-!
# Full point-parabolic movement on the Hermitian nine-space

The point radical already moves the five-space supported on the first row
and column. Lower-block unipotents, a trace-one element, and the lower
coordinate interchange generate the remaining four coordinates. Hence the
full point parabolic has commutator equal to the entire original module.

This supplies the containment V ≤ O₂(C_L(z)^∞) implicit in the literal
quotient O₂(L_z)/V of Aschbacher–Smith 8.2.11(4), printed p.722,
refs/quasithin.pdf; the source extension transports the full residual image.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open Representation.HermitianTensorThree.ImageOuter
namespace Representation.HermitianTensorThree.PointSection
set_option backward.isDefEq.respectTransparency false
local instance : SMul (ZMod 2) (Space 1) := (binaryModule 1).toSMul

private def lowerCoord (a b : F 1) (u : E 1) : Space 1 :=
  (coordinates 1).symm (![0,a,b],![0,0,u])

private theorem lowerCoord_add (a b c d : F 1) (u v : E 1) :
    lowerCoord (a+c) (b+d) (u+v) = lowerCoord a b u + lowerCoord c d v := by
  apply (coordinates 1).injective
  simp only [map_add,lowerCoord,LinearEquiv.apply_symm_apply]
  ext i <;> fin_cases i <;> simp

/-- The whole point parabolic moves the entire Hermitian nine-space. -/
theorem point_parabolic_commutator :
    subspaceCommutator (UnipotentRadicals.ambientAction 1) ⊤
      (ParabolicTorus.pointParabolicImage 1) = ⊤ := by
  let W := subspaceCommutator (UnipotentRadicals.ambientAction 1) ⊤
    (ParabolicTorus.pointParabolicImage 1)
  have hd (a : Cover 1) (ha : a 1 0=0 ∧ a 2 0=0) (X : Space 1) :
      binaryActionHom 1 a X-X ∈ W := by
    apply Submodule.subset_span
    refine ⟨_,mem_map_of_mem _ ?_,X,Submodule.mem_top,rfl⟩
    exact (Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff _ _).mpr ha
  have hm : moved ≤ W := by
    rw [←point_commutator]
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨u,hu,rfl⟩,X,_,rfl⟩
    exact hd (specialLinear _ u) ⟨rfl,rfl⟩ X
  have hu (t : E 1) (X : Space 1) :
      UnipotentRadicals.unipotentHom 1 ⟨0,t,0⟩ X-X ∈ W :=
    hd (specialLinear _ ⟨0,t,0⟩) ⟨rfl,rfl⟩ X
  have h11 : lowerCoord 1 0 0 ∈ W := by
    obtain ⟨t,ht⟩ := FieldSections.exists_trace_one 1
    have he : UnipotentRadicals.unipotentHom 1 ⟨0,1,0⟩ (lowerCoord 0 0 t)-lowerCoord 0 0 t =
        lowerCoord 1 0 0 := by
      apply Subtype.ext
      change matrix (E 1) ⟨0,1,0⟩ * (lowerCoord 0 0 t).val * adjoint 1 (matrix (E 1) ⟨0,1,0⟩) -
        (lowerCoord 0 0 t).val = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerCoord,coordinates,matrix,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_three,ht]
    exact he ▸ hu 1 (lowerCoord 0 0 t)
  let s : Cover 1 := ⟨!![1,0,0;0,0,1;0,1,0],by simp [Matrix.det_fin_three,CharTwo.neg_eq]⟩
  have h22 : lowerCoord 0 1 0 ∈ W := by
    have he : binaryActionHom 1 s (lowerCoord 1 0 0)-lowerCoord 1 0 0 =
        lowerCoord 0 1 0-lowerCoord 1 0 0 := by
      congr 1
      apply Subtype.ext
      change s.val * (lowerCoord 1 0 0).val * adjoint 1 s.val = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [s,lowerCoord,coordinates,adjoint,Matrix.mul_apply,Fin.sum_univ_three]
    exact (Submodule.sub_mem_iff_left _ h11).mp (he ▸ hd s ⟨rfl,rfl⟩ (lowerCoord 1 0 0))
  have hdiag (a b : F 1) : lowerCoord a b 0 ∈ W := by
    have hA : a=0 ∨ a=1 := (eq_zero_or_one_of_sq_eq_self a.property).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    have hB : b=0 ∨ b=1 := (eq_zero_or_one_of_sq_eq_self b.property).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    rcases hA with rfl|rfl <;> rcases hB with rfl|rfl
    · have he : lowerCoord 0 0 0=0 := by apply (coordinates 1).injective; simp [lowerCoord]
      rw [he]; exact W.zero_mem
    · exact h22
    · exact h11
    · simpa only [←lowerCoord_add,zero_add,add_zero] using W.add_mem h11 h22
  have hoff (u : E 1) : lowerCoord 0 0 u ∈ W := by
    let a : F 1 := ⟨u*sigma 1 u,by
      change sigma 1 (u*sigma 1 u)=u*sigma 1 u
      rw [map_mul,sigma_involutive,mul_comm]⟩
    have he : UnipotentRadicals.unipotentHom 1 ⟨0,u,0⟩ (lowerCoord 0 1 0)-lowerCoord 0 1 0 =
        lowerCoord a 0 0+lowerCoord 0 0 u := by
      apply Subtype.ext
      change matrix (E 1) ⟨0,u,0⟩ * (lowerCoord 0 1 0).val * adjoint 1 (matrix (E 1) ⟨0,u,0⟩) -
        (lowerCoord 0 1 0).val = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [a,lowerCoord,coordinates,matrix,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
    exact (Submodule.add_mem_iff_right _ (hdiag a 0)).mp (he ▸ hu u (lowerCoord 0 1 0))
  apply top_unique
  intro X _
  let Y := lowerCoord ((coordinates 1 X).1 1) ((coordinates 1 X).1 2) (X.val 1 2)
  have hY : Y ∈ W := by
    simpa only [←lowerCoord_add,zero_add,add_zero] using W.add_mem
      (hdiag ((coordinates 1 X).1 1) ((coordinates 1 X).1 2)) (hoff (X.val 1 2))
  have hXY : X-Y ∈ moved := by
    exact (mem_moved _).mpr ⟨sub_self _,sub_self _,sub_self _⟩
  exact (Submodule.sub_mem_iff_left _ hY).mp (hm hXY)

end Representation.HermitianTensorThree.PointSection
