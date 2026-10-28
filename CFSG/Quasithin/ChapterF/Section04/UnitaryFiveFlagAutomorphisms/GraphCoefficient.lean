module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.GraphCoordinates
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.BorelNormalization

/-!
# The standard graph coefficient in the literal U₅(4) quotient

Transport the full residual graph formula through the established embedded
residual coordinates. Its PSL₂(16) action is exactly entrywise Hermitian
conjugation. Removing that same graph from a quotient-normalized actor gives
identity on the literal quotient, with no matrix representation assumed.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The standard graph automorphism as an actual native flag actor. -/
def graphFlag : flagAutomorphisms U := ⟨GraphFixed.projectiveAut U.form U.matrix,
  Descent.graph_flag U.form U.matrix⟩

@[simp] theorem graphFlag_val : (graphFlag U).val = GraphFixed.projectiveAut U.form U.matrix := rfl

theorem graphFlag_square : graphFlag U ^ 2 = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact GraphFixed.projectiveAut_involutive U.form U.matrix x

/-- The fixed radical–SL₂ coordinates of the literal embedded residual. -/
def rightCoordinates : PlaneCore.PlaneSemidirect U.form ≃* U.rightLocalImage :=
  U.rightLocalEquiv.trans U.rightLocalImageEquiv

theorem rightCoordinates_val (p : PlaneCore.PlaneSemidirect U.form) :
    (rightCoordinates U p).val =
      FlagAutomorphisms.nativePlane U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix p := by
  change (U.rightLocalImageEquiv (U.rightLocalEquiv p)).val = _
  rw [U.rightLocalImageEquiv_val,U.rightLocalEquiv_val]
  rfl

@[simp] theorem rightQuotientProjection_coordinates (p : PlaneCore.PlaneSemidirect U.form) :
    rightQuotientProjection U (rightCoordinates U p) = Theory.PSL2.quotientMap U.F p.right := by
  change rightQuotientProjection U (U.rightLocalImageEquiv (U.rightLocalEquiv p)) = _
  rw [rightQuotientProjection_equiv,U.rightLocalProjection_equiv]

/-- Graph on the entire embedded plane residual, including its radical correction. -/
theorem rightLocalAction_graph (p : PlaneCore.PlaneSemidirect U.form) :
    rightLocalAction U (graphFlag U) (rightCoordinates U p) =
      rightCoordinates U (FlagAutomorphisms.graphPlaneCoordinates U.form p) := by
  apply Subtype.ext
  rw [rightLocalAction_val,rightCoordinates_val,rightCoordinates_val,graphFlag_val]
  exact FlagAutomorphisms.graph_nativePlane U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix p

/-- Graph has the exact entrywise Hermitian action in the literal PSL₂ quotient. -/
theorem rightLinearAction_graph :
    rightLinearAction U (graphFlag U) = Theory.PSL2.fieldAut U.form.conj := by
  apply MulEquiv.ext
  intro y
  obtain ⟨A,rfl⟩ := Theory.PSL2.quotientMap_surjective U.F y
  have h := rightQuotientProjection_action U (graphFlag U)
    (rightCoordinates U (SemidirectProduct.inr A))
  rw [rightLocalAction_graph,rightQuotientProjection_coordinates,
    rightQuotientProjection_coordinates,FlagAutomorphisms.graphPlaneCoordinates_right] at h
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  exact h.symm

theorem rightCoefficient_graph : rightCoefficient U (graphFlag U) = U.form.conj := by
  change Theory.PSL2.fieldProjection U.F (rightLinearAction U (graphFlag U)) = _
  rw [rightLinearAction_graph,Theory.PSL2.fieldProjection_fieldAut]

/-- Removing the standard graph leaves identity on the actual residual quotient. -/
theorem normalize_graph (β : flagAutomorphisms U)
    (hβ : rightLinearAction U β = Theory.PSL2.fieldAut U.form.conj) :
    ∃ γ : flagAutomorphisms U, β = γ * graphFlag U ∧ rightLinearAction U γ = 1 := by
  refine ⟨β * (graphFlag U)⁻¹,?_,?_⟩
  · simp
  · rw [map_mul,map_inv,rightLinearAction_graph,hβ,mul_inv_cancel]

end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
