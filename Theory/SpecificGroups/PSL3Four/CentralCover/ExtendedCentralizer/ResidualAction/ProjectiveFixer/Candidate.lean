module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Model

/-!
# The explicit candidate for the projective pointwise fixer

Inverse transpose times Frobenius fixes both the diagonal factor and the
three-cycle of the Sylow subgroup in `Model`. It is an involution and commutes
with inner conjugation by that subgroup. Multiplication therefore defines an
actual homomorphism from `model × C₂` into `MulAut PSL`; its image has order
dividing eighteen and fixes the model pointwise.

The converse containment still requires the matrix calculation. The separate
`standardForm` definition records the linear, field and graph parameters for
that calculation, without assuming they exhaust the standard subgroup.

Source: the matrix calculation underlying Aschbacher--Smith 15.3.38,
printed pp.1136--1137, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

def graphField : MulAut PSL := PSL3.OuterSolvable.graph F * pslFrobenius

theorem graph_commute_field : Commute (PSL3.OuterSolvable.graph F) pslFrobenius := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H A =>
    change project (SpecialLinearGroup.transpose (slFrobenius A))⁻¹ =
      project (slFrobenius (SpecialLinearGroup.transpose A)⁻¹)
    rw [map_inv slFrobenius]
    congr 2

theorem graphField_sq : graphField ^ 2 = 1 := by
  rw [graphField, graph_commute_field.mul_pow, PSL3.OuterSolvable.graph_sq,
    pslFrobenius_sq, one_mul]

private theorem transpose_diagonal (u : Fˣ) :
    SpecialLinearGroup.transpose (diagonalSL u) = diagonalSL u := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem frobenius_diagonal (u : Fˣ) :
    slFrobenius (diagonalSL u) = diagonalSL u⁻¹ := by
  apply SpecialLinearGroup.ext
  intro i j
  have hi : (↑u⁻¹ : F) = (u : F)^2 := congrArg Units.val (unit_inv u)
  change ((!![1,0,0;0,(u : F),0;0,0,↑u⁻¹] : Matrix (Fin 3) (Fin 3) F) i j)^2 =
    (!![1,0,0;0,(↑u⁻¹ : F),0;0,0,(↑(u⁻¹)⁻¹ : F)] : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp [hi, ← pow_mul, pow_four]

theorem graphField_diagonal (u : Fˣ) : graphField (diagonal u) = diagonal u := by
  change project (SpecialLinearGroup.transpose (slFrobenius (diagonalSL u)))⁻¹ =
    project (diagonalSL u)
  rw [frobenius_diagonal, transpose_diagonal, ← map_inv, inv_inv]

private theorem frobenius_cycle : slFrobenius cycleSL = cycleSL := by
  apply SpecialLinearGroup.ext
  intro i j
  change ((!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) i j)^2 =
    (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem transpose_cycle : SpecialLinearGroup.transpose cycleSL = cycleSL⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply Subtype.ext
  change (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) *
    (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F).transpose = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem graphField_cycle : graphField cycle = cycle := by
  change project (SpecialLinearGroup.transpose (slFrobenius cycleSL))⁻¹ = project cycleSL
  rw [frobenius_cycle, transpose_cycle, inv_inv]

theorem graphField_fixes_model : model ≤ graphField.fixedSubgroup := by
  rw [model_eq]
  apply sup_le
  · rintro x ⟨u, rfl⟩
    exact (MulAut.mem_fixedSubgroup _ _).mpr (graphField_diagonal u)
  · apply zpowers_le.mpr
    exact (MulAut.mem_fixedSubgroup _ _).mpr graphField_cycle

theorem model_commute (x y : model) : Commute (x : PSL) (y : PSL) := by
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  rw [← ha, ← hb]
  exact (show Commute a b from Prod.ext (mul_comm _ _)
    (IsMulCommutative.is_comm.comm _ _)).map embedding

def modelInner : model →* MulAut PSL := MulAut.conj.comp model.subtype

theorem modelInner_commute_graphField (x : model) : Commute (modelInner x) graphField := by
  apply MulEquiv.ext
  intro y
  have hx : graphField (x : PSL) = x := (MulAut.mem_fixedSubgroup _ _).mp
    (graphField_fixes_model x.property)
  change (x : PSL) * graphField y * (x : PSL)⁻¹ =
    graphField ((x : PSL) * y * (x : PSL)⁻¹)
  rw [map_mul, map_mul, map_inv, hx]

def candidateHom : model × C2 →* MulAut PSL :=
  modelInner.noncommCoprod (involutionHom graphField graphField_sq) (by
    intro x t
    exact (modelInner_commute_graphField x).pow_right t.toAdd.val)

def candidate : Subgroup (MulAut PSL) := candidateHom.range

theorem candidate_card_dvd : Nat.card candidate ∣ 18 := by
  have h := card_range_dvd candidateHom
  simpa only [candidate, Nat.card_prod, model_card, card_C2] using h

theorem candidate_fixes_model : candidate ≤ fixingSubgroup (MulAut PSL) (model : Set PSL) := by
  rintro a ⟨⟨x, t⟩, rfl⟩ y
  have hx : (modelInner x) y.val = y.val := by
    change (x : PSL) * y.val * (x : PSL)⁻¹ = y.val
    rw [(model_commute x y).eq, mul_inv_cancel_right]
  have ht : (involutionHom graphField graphField_sq t) y.val = y.val := by
    have hy := (MulAut.mem_fixedSubgroup _ _).mp (graphField_fixes_model y.property)
    exact smul_eq_self_of_mem_zpowers (npow_mem_zpowers graphField t.toAdd.val) hy
  change modelInner x ((involutionHom graphField graphField_sq t) y.val) = y.val
  rw [ht, hx]

theorem frobenius_eq_fieldAction : pslFrobenius =
    PSL3.OuterSolvable.fieldAction F fieldFrobenius := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H A =>
    rw [pslFrobenius_mk, PSL3.OuterSolvable.fieldAction_mk]
    rfl

theorem candidate_le_standard : candidate ≤ PSL3.OuterSolvable.standard F := by
  rintro a ⟨⟨x, t⟩, rfl⟩
  apply (PSL3.OuterSolvable.standard F).mul_mem
  · exact PSL3.OuterSolvable.inner_le_standard F ⟨(x : PSL), rfl⟩
  · apply (PSL3.OuterSolvable.standard F).pow_mem
    apply (PSL3.OuterSolvable.standard F).mul_mem
    · exact PSL3.OuterSolvable.graph_mem_standard F
    · rw [frobenius_eq_fieldAction]
      exact PSL3.OuterSolvable.fieldAction_mem_standard F fieldFrobenius

def standardForm (A : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F) (t : C2) :
    MulAut PSL :=
  PSL3.OuterSolvable.linearConj F A * PSL3.OuterSolvable.fieldAction F σ *
    involutionHom (PSL3.OuterSolvable.graph F) (PSL3.OuterSolvable.graph_sq F) t

theorem standardForm_mem (A : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F) (t : C2) :
    standardForm A σ t ∈ PSL3.OuterSolvable.standard F := by
  apply (PSL3.OuterSolvable.standard F).mul_mem
  · exact (PSL3.OuterSolvable.standard F).mul_mem
      (PSL3.OuterSolvable.linearConj_mem_standard F A)
      (PSL3.OuterSolvable.fieldAction_mem_standard F σ)
  · exact (PSL3.OuterSolvable.standard F).pow_mem
      (PSL3.OuterSolvable.graph_mem_standard F) t.toAdd.val

end Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
