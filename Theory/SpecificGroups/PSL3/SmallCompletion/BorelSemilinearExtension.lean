module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourCoordinates
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity

/-!
# Actual simultaneous semilinear extension across both endpoints

A diagonal GL₃ conjugation followed by field transport realizes the common
root scalars and field automorphism. The literal point, line, and Borel
subgroups and the full projective torus are preserved.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The actual ambient diagonal/field actor with prescribed simple-root scalars. -/
@[expose] def rootSemilinearActor (r s : Fˣ) (σ : F ≃+* F) : MulAut PSL(3,F) :=
  linearConj F (diagonalGL ![r*s,s,1]) * fieldAction F σ

private def rootSemilinearSL (r s : Fˣ) (σ : F ≃+* F) (g : SL(3,F)) : SL(3,F) :=
  linearConjSL F (diagonalGL ![r*s,s,1]) (SpecialLinearGroup.map σ.toRingHom g)

omit [Finite F] in
private theorem rootSemilinear_mk (r s : Fˣ) (σ : F ≃+* F) (g : SL(3,F)) :
    rootSemilinearActor F r s σ (projection F g)=projection F (rootSemilinearSL F r s σ g) := by
  change (linearConj F (diagonalGL ![r*s,s,1]))
    (fieldAction F σ (QuotientGroup.mk g))=QuotientGroup.mk _
  rw [fieldAction_mk,linearConj_mk]
  rfl

omit [Finite F] in
private theorem rootSemilinear_entry (r s : Fˣ) (σ : F ≃+* F) (g : SL(3,F))
    (i j : Fin 3) :
    (rootSemilinearSL F r s σ g).val i j =
      ((![r*s,s,1] i : Fˣ):F)*σ (g.val i j)*((![r*s,s,1] j : Fˣ):F)⁻¹ := by
  have hh := congrArg Units.val (linearConjSL_toGL F (diagonalGL ![r*s,s,1])
    (SpecialLinearGroup.map σ.toRingHom g))
  rw [Units.val_mul,Units.val_mul,SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix] at hh
  rw [←Units.inv_eq_val_inv] at hh
  have he : (rootSemilinearSL F r s σ g).val =
      Matrix.diagonal (fun i => ((![r*s,s,1] i : Fˣ):F))*
        g.val.map σ.toRingHom*Matrix.diagonal (fun i => ((![r*s,s,1] i : Fˣ):F)⁻¹) := by
    simpa only [diagonalGL,Units.val_inv_eq_inv_val,SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,rootSemilinearSL] using hh
  rw [he]
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply]
  rfl

omit [Finite F] in
/-- Exact common root scalars and field map on the original unipotent subgroup. -/
theorem rootSemilinearActor_unipotent (r s : Fˣ) (σ : F ≃+* F) (u : U F) :
    rootSemilinearActor F r s σ (projective F u)=
      projective F ⟨r*σ u.x,s*σ u.y,(r:F)*s*σ u.c⟩ := by
  rw [show projective F u=projection F (specialLinear F u) from rfl,rootSemilinear_mk]
  apply congrArg (projection F)
  apply Subtype.ext
  funext i j
  rw [rootSemilinear_entry]
  change ((![r*s,s,1] i : Fˣ):F)*σ (matrix F u i j)*((![r*s,s,1] j : Fˣ):F)⁻¹ =
    matrix F ⟨r*σ u.x,s*σ u.y,(r:F)*s*σ u.c⟩ i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,mul_assoc]
  all_goals field_simp

/-- The whole torus has exactly the specified field action. -/
theorem rootSemilinearActor_torus (r s : Fˣ) (σ : F ≃+* F) (t : Fˣ) :
    rootSemilinearActor F r s σ (simultaneousTorus F t : PSL(3,F))=
      (simultaneousTorus F (Units.map σ.toMonoidHom t) : PSL(3,F)) := by
  change rootSemilinearActor F r s σ (projection F (torusSL F (t,t⁻¹)))=
    projection F (torusSL F (_,_))
  rw [rootSemilinear_mk]
  apply congrArg (projection F)
  apply Subtype.ext
  funext i j
  rw [rootSemilinear_entry]
  fin_cases i <;> fin_cases j <;>
    simp [torusSL_val,mul_assoc,mul_left_comm,mul_comm]
  all_goals field_simp

private theorem map_eq_of_mapsTo (a : MulAut PSL(3,F)) (H : Subgroup PSL(3,F))
    (h : ∀ x∈H,a x∈H) : H.map a.toMonoidHom=H := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · rw [←Nat.card_congr (H.equivMapOfInjective a.toMonoidHom a.injective).toEquiv]

/-- Both original local endpoints and their whole Borel are preserved. -/
theorem rootSemilinearActor_endpoints (r s : Fˣ) (σ : F ≃+* F) :
    (pointLocal F).map (rootSemilinearActor F r s σ).toMonoidHom=pointLocal F ∧
    (lineLocal F).map (rootSemilinearActor F r s σ).toMonoidHom=lineLocal F ∧
    (borel F).map (rootSemilinearActor F r s σ).toMonoidHom=borel F := by
  constructor
  · apply map_eq_of_mapsTo
    rintro _ ⟨g,hg,rfl⟩
    rw [rootSemilinear_mk]
    apply mem_map_of_mem
    obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F _).mp hg
    rw [mem_pointLocalSL_iff]
    simp [rootSemilinear_entry,h00,h10,h20]
    field_simp
  constructor
  · apply map_eq_of_mapsTo
    rintro _ ⟨g,hg,rfl⟩
    rw [rootSemilinear_mk]
    apply mem_map_of_mem
    obtain ⟨h20,h21,h22⟩ := (mem_lineLocalSL_iff F _).mp hg
    rw [mem_lineLocalSL_iff]
    simp [rootSemilinear_entry,h20,h21,h22]
  · apply map_eq_of_mapsTo
    rintro _ ⟨g,hg,rfl⟩
    rw [rootSemilinear_mk]
    apply mem_map_of_mem
    obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F _).mp hg
    rw [mem_borelSL_iff]
    simp [rootSemilinear_entry,h10,h20,h21]

end Matrix.PSL3.SmallCompletion
