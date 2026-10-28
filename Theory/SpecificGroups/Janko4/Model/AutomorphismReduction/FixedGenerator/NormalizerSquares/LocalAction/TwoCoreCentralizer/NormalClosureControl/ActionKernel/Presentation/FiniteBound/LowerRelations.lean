module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Stabilizers
public import Mathlib.Tactic.FinCases

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
open Subgroup.CosetWordCertificate

private theorem equal_generators :
    (PresentedGroup.of (1 : Fin 7) : Level1) = PresentedGroup.of 0 := by
  have h := level1_relator 2
  change eval (PresentedGroup.of : Fin 7 → Level1) [(0, false), (1, true)] = 1 at h
  symm
  simpa [eval_cons, inv_mul_eq_one] using h

public theorem liftedRelations12 : LiftedRelations12 := by
  intro i
  fin_cases i
  · exact level1_relator 0
  · exact level1_relator 1
  · have h := level1_relator 3
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, false), (1, false), (0, false)] = 1 at h
    simp only [eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte, mul_one, equal_generators] at h
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, true), (0, true), (0, true)] = 1
    simpa only [eval_cons, eval_nil, ↓reduceIte, mul_one, mul_inv_rev, inv_inv, inv_one,
      mul_assoc] using congrArg Inv.inv h
  · have h := level1_relator 6
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, true), (6, true), (1, false), (6, true)] = 1 at h
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, true), (6, true), (0, false), (6, true)] = 1
    simpa only [eval_cons, equal_generators] using h
  · have h := level1_relator 5
    have hb := level1_relator 0
    change eval (PresentedGroup.of : Fin 7 → Level1) [(5, true), (5, true)] = 1 at hb
    simp only [eval_cons, eval_nil, ↓reduceIte, mul_one] at hb
    have hi : (PresentedGroup.of (5 : Fin 7) : Level1)⁻¹ = PresentedGroup.of 5 :=
      inv_eq_of_mul_eq_one_left hb
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, true), (5, true), (1, true), (5, true)] = 1 at h
    simp only [eval_cons, eval_nil, ↓reduceIte, mul_one, equal_generators] at h
    change eval (PresentedGroup.of : Fin 7 → Level1) [(0, false), (5, true), (0, false), (5, true)] = 1
    simp only [eval_cons, eval_nil, Bool.false_eq_true, ↓reduceIte, mul_one]
    have hh := congrArg Inv.inv h
    simp only [mul_inv_rev, inv_one, hi] at hh
    simp only [mul_assoc] at hh
    simpa only [mul_assoc] using (mul_eq_one_comm.mp hh)
  · exact level1_relator 9

public theorem liftedRelations23 : LiftedRelations23 := by
  intro i
  fin_cases i
  · exact level2_relator 0
  · exact level2_relator 1
  · exact level2_relator 5

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
