module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelSemilinearExtension
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl
public import Theory.GroupTheory.SylowKernelCore

/-!
# Physical scalar changes fixing the first reflection

A diagonal automorphism of the whole projective linear group fixes the
point reflection and every torus element. It scales both point-radical
coordinates by the same arbitrary nonzero scalar, and preserves both full
parabolics. Transporting this automorphism through a full linear marking
therefore changes physical generators while retaining the first reflection,
the cubic torus, and both endpoint carriers.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The full-group diagonal actor with scalar action on the point radical. -/
@[expose] def firstReflectionScalarActor (k : Fˣ) : MulAut PSL(3,F) :=
  rootSemilinearActor F k 1 (RingEquiv.refl F)

omit [Finite F] in
private theorem first_reflection_fixed_SL (k : Fˣ) :
    linearConjSL F (diagonalGL ![k,1,1]) (reflectionSL F false) =
      reflectionSL F false := by
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  simp only [Units.val_mul,SpecialLinearGroup.coe_GL_coe_matrix,
    ←Units.inv_eq_val_inv]
  simp only [diagonalGL,Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionSL,Matrix.diagonal_mul,Matrix.mul_diagonal]

omit [Finite F] in
/-- The literal point reflection is fixed, rather than merely conjugate. -/
theorem firstReflectionScalarActor_reflection (k : Fˣ) :
    firstReflectionScalarActor F k (reflection F false) = reflection F false := by
  change linearConj F (diagonalGL ![k*1,1,1])
    (fieldAction F (RingEquiv.refl F) (projection F (reflectionSL F false))) = _
  rw [show fieldAction F (RingEquiv.refl F)=1 from map_one _]
  change linearConj F (diagonalGL ![k*1,1,1])
    (QuotientGroup.mk (reflectionSL F false)) = _
  rw [linearConj_mk]
  rw [mul_one,first_reflection_fixed_SL]
  rfl

omit [CharP F 2] in
/-- Every element of the original split torus is fixed. -/
theorem firstReflectionScalarActor_torus (k t : Fˣ) :
    firstReflectionScalarActor F k (simultaneousTorus F t : PSL(3,F)) =
      (simultaneousTorus F t : PSL(3,F)) := by
  have h := rootSemilinearActor_torus F k 1 (RingEquiv.refl F) t
  have ht : Units.map (RingEquiv.refl F).toMonoidHom t = t := Units.ext rfl
  rw [ht] at h
  exact h

omit [Finite F] [CharP F 2] in
private theorem diagonal_torus_fixed_SL (k : Fˣ) (d : Fˣ × Fˣ) :
    linearConjSL F (diagonalGL ![k,1,1]) (torusSL F d) = torusSL F d := by
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  simp only [Units.val_mul,SpecialLinearGroup.coe_GL_coe_matrix,
    ←Units.inv_eq_val_inv]
  simp only [diagonalGL,Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusSL_val,Matrix.mul_diagonal,mul_assoc,mul_comm]
  field_simp

omit [Finite F] [CharP F 2] in
/-- The physical diagonal actor fixes every element of the full projective torus. -/
theorem firstReflectionScalarActor_fixes_full_torus (k : Fˣ) (x : PSL(3,F))
    (hx : x ∈ torus F) : firstReflectionScalarActor F k x = x := by
  obtain ⟨d,rfl⟩ := hx
  change linearConj F (diagonalGL ![k*1,1,1])
    (fieldAction F (RingEquiv.refl F) (projection F (torusSL F d))) = _
  rw [show fieldAction F (RingEquiv.refl F)=1 from map_one _]
  change linearConj F (diagonalGL ![k*1,1,1])
    (QuotientGroup.mk (torusSL F d)) = _
  rw [linearConj_mk,mul_one,diagonal_torus_fixed_SL]
  rfl

omit [Finite F] [CharP F 2] in
/-- Both coordinates of the actual point radical are multiplied by k. -/
theorem firstReflectionScalarActor_point_radical (k : Fˣ) (x c : F) :
    firstReflectionScalarActor F k (projective F ⟨x,0,c⟩) =
      projective F ⟨k*x,0,k*c⟩ := by
  simpa only [firstReflectionScalarActor,RingEquiv.refl_apply,Units.val_one,
    one_mul,mul_one] using
    rootSemilinearActor_unipotent F k 1 (RingEquiv.refl F) ⟨x,0,c⟩

omit [CharP F 2] in
/-- Both full endpoint groups and their literal common Borel are retained. -/
theorem firstReflectionScalarActor_endpoints (k : Fˣ) :
    (pointParabolic F).map (firstReflectionScalarActor F k).toMonoidHom =
      pointParabolic F ∧
    (lineParabolic F).map (firstReflectionScalarActor F k).toMonoidHom =
      lineParabolic F ∧
    (borel F).map (firstReflectionScalarActor F k).toMonoidHom = borel F := by
  dsimp only [firstReflectionScalarActor]
  obtain ⟨hP,hQ,hB⟩ := rootSemilinearActor_endpoints F k 1 (RingEquiv.refl F)
  refine ⟨?_,?_,hB⟩
  · rw [pointParabolic_eq_sup,Subgroup.map_sup,hP,hB]
  · rw [lineParabolic_eq_sup,Subgroup.map_sup,hQ,hB]

/-- Every scalar is realized by an automorphism of the original full linear
carrier, fixing its prescribed first reflection and torus elements while
retaining both endpoint groups and their entire two-cores. -/
theorem exists_original_first_reflection_scalar_actor
    {H : Type*} [Group H] (e : H ≃* PSL(3,F))
    (P Q : Subgroup H)
    (hP : P.map e.toMonoidHom = pointParabolic F)
    (hQ : Q.map e.toMonoidHom = lineParabolic F) (k : Fˣ) :
    ∃ α : MulAut H,
      (∀ g, e (α g) = firstReflectionScalarActor F k (e g)) ∧
      (∀ r, e r = reflection F false → α r = r) ∧
      (∀ t, ∀ τ : Fˣ, e t = (simultaneousTorus F τ : PSL(3,F)) → α t = t) ∧
      P.map α.toMonoidHom = P ∧ Q.map α.toMonoidHom = Q ∧
      (P.pCoreIn 2).map α.toMonoidHom = P.pCoreIn 2 ∧
      (Q.pCoreIn 2).map α.toMonoidHom = Q.pCoreIn 2 := by
  let a := firstReflectionScalarActor F k
  let α : MulAut H := (e.trans a).trans e.symm
  have he (g : H) : e (α g) = a (e g) := e.apply_symm_apply _
  have hcomp : e.toMonoidHom.comp α.toMonoidHom =
      a.toMonoidHom.comp e.toMonoidHom := MonoidHom.ext he
  obtain ⟨haP,haQ,_⟩ := firstReflectionScalarActor_endpoints F k
  have hαP : P.map α.toMonoidHom = P := by
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    rw [Subgroup.map_map,hcomp,←Subgroup.map_map,hP]
    exact haP
  have hαQ : Q.map α.toMonoidHom = Q := by
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    rw [Subgroup.map_map,hcomp,←Subgroup.map_map,hQ]
    exact haQ
  refine ⟨α,he,?_,?_,hαP,hαQ,?_,?_⟩
  · intro r hr
    apply e.injective
    rw [he,hr]
    exact firstReflectionScalarActor_reflection F k
  · intro t τ ht
    apply e.injective
    rw [he,ht]
    exact firstReflectionScalarActor_torus F k τ
  · rw [Subgroup.map_pCoreIn_of_injective 2 P α.toMonoidHom α.injective,hαP]
  · rw [Subgroup.map_pCoreIn_of_injective 2 Q α.toMonoidHom α.injective,hαQ]

end Matrix.PSL3.SmallCompletion
