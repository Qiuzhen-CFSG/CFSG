module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Model
public import Theory.SpecificGroups.PSL3.CartanActions
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity

/-!
# The standard three-line frame in the natural SL₃ model

The fixed line of the upper Sylow is the first coordinate line.  The reversal
and the cyclic permutation give the other two coordinate lines.  These are
the only model calculations needed when a source lift is transported back to
the original right-conjugation convention.
Source: Aschbacher–Smith 11.5.7, printed p.781.
-/

open Matrix Submodule Representation
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
open scoped MatrixGroups

@[expose] public section

namespace Matrix.SpecialLinearGroup.FrameGeometry

variable {F : Type*} [Field F]

/-- The three coordinate vectors. -/
def coordinateVector (i : Fin 3) : Fin 3 → F := Pi.single i 1

/-- The three coordinate lines. -/
def coordinateLine (i : Fin 3) : Submodule F (Fin 3 → F) :=
  Submodule.span F {coordinateVector (F := F) i}

theorem coordinateVector_ne_zero (i : Fin 3) :
    coordinateVector (F := F) i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [coordinateVector] at hi

theorem coordinateVector_not_mem_line {i j : Fin 3} (hij : i ≠ j) :
    coordinateVector (F := F) i ∉ coordinateLine (F := F) j := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hi := congrFun ha i
  simp [coordinateVector, hij] at hi

theorem coordinateLine_disjoint {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (coordinateLine (F := F) i) (coordinateLine j) := by
  exact Submodule.disjoint_span_singleton_of_notMem
    (coordinateVector_not_mem_line hij.symm)

theorem coordinateLine_01_finrank :
    Module.finrank F ↥((coordinateLine (F := F) 0) ⊔ coordinateLine 1) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (coordinateLine (F := F) 0) (coordinateLine 1)
  have h0 : Module.finrank F ↥(coordinateLine (F := F) 0) = 1 := by
    change Module.finrank F (F ∙ coordinateVector (F := F) 0) = 1
    exact finrank_span_singleton (coordinateVector_ne_zero (F := F) 0)
  have h1 : Module.finrank F ↥(coordinateLine (F := F) 1) = 1 := by
    change Module.finrank F (F ∙ coordinateVector (F := F) 1) = 1
    exact finrank_span_singleton (coordinateVector_ne_zero (F := F) 1)
  rw [(coordinateLine_disjoint (F := F) (by decide)).eq_bot, finrank_bot,
    h0, h1, add_zero] at h
  exact h

theorem coordinateLine_01_not_mem_2 :
    coordinateVector (F := F) 2 ∉
      coordinateLine (F := F) 0 ⊔ coordinateLine 1 := by
  intro h
  rcases Submodule.mem_sup.mp h with ⟨v, hv, w, hw, he⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hw
  have h2 := congrFun he 2
  have h20 := congrFun ha 2
  have h21 := congrFun hb 2
  simp [coordinateVector] at h2 h20 h21
  rw [← h20, ← h21] at h2
  simp at h2

theorem coordinateLine_01_disjoint_2 :
    Disjoint (coordinateLine (F := F) 0 ⊔ coordinateLine 1)
      (coordinateLine 2) := by
  exact Submodule.disjoint_span_singleton_of_notMem
    (coordinateLine_01_not_mem_2 (F := F))

theorem coordinateFrame_span :
    (coordinateLine (F := F) 0 ⊔ coordinateLine 1) ⊔ coordinateLine 2 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (coordinateLine (F := F) 0 ⊔ coordinateLine 1) (coordinateLine 2)
  have h2 : Module.finrank F ↥(coordinateLine (F := F) 2) = 1 := by
    change Module.finrank F (F ∙ coordinateVector (F := F) 2) = 1
    exact finrank_span_singleton (coordinateVector_ne_zero (F := F) 2)
  rw [(coordinateLine_01_disjoint_2 (F := F)).eq_bot, finrank_bot,
    coordinateLine_01_finrank (F := F), h2, add_zero] at h
  simpa [Module.finrank_fin_fun] using h

/-- The ordered coordinate frame. -/
def coordinateFrame : Frame F := {
  point := ![coordinateLine 0, coordinateLine 1, coordinateLine 2]
  dimension := by
    intro i
    fin_cases i <;> apply finrank_span_singleton <;>
      apply coordinateVector_ne_zero
  disjoint := coordinateLine_disjoint (by decide)
  third_disjoint := coordinateLine_01_disjoint_2
  span := coordinateFrame_span }

theorem coordinateLine_eq_model_point :
    coordinateLine (F := F) 0 =
      CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.Model.point := by
  ext v
  change v ∈ Submodule.span F {coordinateVector (F := F) 0} ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.Model.point,
      coordinateVector]
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [coordinateVector, hv.1, hv.2]

theorem reversal_apply_coordinate_zero [CharP F 2] :
    specialLinearNatural 3 (reversalSL F) (coordinateVector (F := F) 0) =
      coordinateVector 2 := by
  rw [specialLinearNatural_apply]
  change (fun i => ∑ j : Fin 3, (reversalSL F).val i j *
    coordinateVector (F := F) 0 j) = coordinateVector 2
  ext i
  fin_cases i <;> simp [reversalSL, reversalGL, coordinateVector, Fin.sum_univ_three]

def cycleGL : GL (Fin 3) F where
  val := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  inv := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]

def cycleSL : SL(3,F) := ⟨(cycleGL (F := F)).val, by
  simp [cycleGL, Matrix.det_fin_three]⟩

theorem cycle_apply_coordinate_zero :
    specialLinearNatural 3 (cycleSL (F := F)) (coordinateVector (F := F) 0) =
      coordinateVector 1 := by
  rw [specialLinearNatural_apply]
  change (fun i => ∑ j : Fin 3, (cycleSL (F := F)).val i j *
    coordinateVector (F := F) 0 j) = coordinateVector 1
  ext i
  fin_cases i <;> simp [cycleSL, cycleGL, coordinateVector, Fin.sum_univ_three]

theorem reversal_maps_coordinateLine [CharP F 2] :
    (coordinateLine (F := F) 0).map
      (specialLinearNatural 3 (reversalSL F)) = coordinateLine 2 := by
  change Submodule.map (specialLinearNatural 3 (reversalSL F))
    (Submodule.span F {coordinateVector (F := F) 0}) = _
  rw [Submodule.map_span, Set.image_singleton,
    reversal_apply_coordinate_zero]
  rfl

theorem cycle_maps_coordinateLine :
    (coordinateLine (F := F) 0).map
      (specialLinearNatural 3 (cycleSL (F := F))) = coordinateLine 1 := by
  change Submodule.map (specialLinearNatural 3 (cycleSL (F := F)))
    (Submodule.span F {coordinateVector (F := F) 0}) = _
  rw [Submodule.map_span, Set.image_singleton, cycle_apply_coordinate_zero]
  rfl

end Matrix.SpecialLinearGroup.FrameGeometry
