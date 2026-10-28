module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Model
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor
/-!
# Weyl elements on the full diagonal Cartan

The coordinate cycle and reversal normalize the full SL₃ diagonal torus.
Their natural actions carry the first coordinate line to the other two,
and one common change of basis transports these actions to the source flag.
Source: Aschbacher–Smith 11.5.7, printed p.781.
-/

open Matrix Subgroup Representation
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry
variable {F : Type*} [Field F]

theorem cycleSL_toGL : SpecialLinearGroup.toGL (cycleSL (F := F)) = cycleGL :=
  Units.ext rfl

theorem cycle_conjugates_torus (d : Fˣ × Fˣ) :
    cycleSL * torusSL F d * cycleSL⁻¹ = torusSL F (d.2, (d.1 * d.2)⁻¹) := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, cycleSL_toGL]
  apply Units.ext
  change (cycleGL (F := F)).val * (torusSL F d).val * cycleGL.inv = _
  rw [torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      torusSL_val, mul_comm]

theorem cycle_normalizes_torus [Finite F] :
    cycleSL (F := F) ∈ normalizer ((torusSL F).range : Set SL(3,F)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨d, ⟨u,rfl⟩, rfl⟩
    exact ⟨(u.2, (u.1 * u.2)⁻¹), (cycle_conjugates_torus u).symm⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj cycleSL).injective]

theorem reversal_normalizes_torus [Finite F] [CharP F 2] :
    reversalSL F ∈ normalizer ((torusSL F).range : Set SL(3,F)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨d, ⟨u,rfl⟩, rfl⟩
    refine ⟨(u.2, u.1), ?_⟩
    have h := linearConjSL_reversal_torusSL F u
    rw [← reversalSL_toGL, SixCommutators.linearConjSL_toGL_inner] at h
    exact h.symm
  · rw [Subgroup.card_map_of_injective (MulAut.conj (reversalSL F)).injective]

/-- The natural action carries products to successive images of subspaces. -/
theorem line_map_mul (U : Submodule F (Fin 3 → F)) (a b : SL(3,F)) :
    U.map (specialLinearNatural 3 (a * b)) =
      (U.map (specialLinearNatural 3 b)).map (specialLinearNatural 3 a) := by
  rw [← Submodule.map_comp, map_mul]
  rfl

/-- Conjugating a Weyl element transports its action on the selected coordinate line. -/
theorem transported_line (g w : SL(3,F)) (i : Fin 3)
    (hw : (coordinateLine (F := F) 0).map (specialLinearNatural 3 w) = coordinateLine i) :
    ((coordinateLine (F := F) 0).map (specialLinearNatural 3 g)).map
      (specialLinearNatural 3 (g * w * g⁻¹)) =
      (coordinateLine (F := F) i).map (specialLinearNatural 3 g) := by
  rw [← line_map_mul]
  rw [show g * w * g⁻¹ * g = g * w by group]
  rw [line_map_mul, hw]
end Matrix.SpecialLinearGroup.FrameGeometry
