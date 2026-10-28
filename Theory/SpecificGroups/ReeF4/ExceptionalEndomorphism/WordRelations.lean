module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Lift

/-!
# Exceptional root substitution preserves the concrete F4 relations

Words are evaluated in the units of the actual Cartan-plus-root matrix algebra
over each Ree coefficient field. Exceptional substitution sends a root to its
positive length-interchanging dual and squares exactly the geometrically short
root parameters. Every word evaluating to one still evaluates to one after
this substitution.

The singular quotient-to-ideal matrix intertwines the two evaluations on
generators, hence on all words by `lift_intertwines`. A relation therefore has
twisted evaluation fixing the short ideal. This evaluation belongs to the
actual root-generated matrix group, whose proved faithful action on that ideal
forces it to be one. All intertwining and faithfulness premises are discharged.

The root formula is the characteristic-two F4 case of Steinberg, *Lectures on
Chevalley Groups*, Theorem 28 (`refs/KGroup/GLS3/Chapter2St1.tex`, pp. 147–148),
also stated in GLS, Theorem 1.15.4(b) (`refs/KGroup/GLS3/Chapter1.tex`). Here its
relation-preservation assertion is proved directly for the integral matrices;
no abstract presentation or algebraic-group existence theorem is used. The
Ree family appears in Aschbacher–Smith, Remark A.2.4 (`refs/quasithin.pdf`).
-/

public section

open Theory.AlgebraicGroup
open scoped Matrix

namespace ReeF4.WordRelations

/-- Evaluation of free words in the concrete F4 root curves. -/
@[expose] noncomputable def eval (m : ℕ) :
    FreeGroup (F4Chevalley.Root × CoefficientField m) →*
      (Matrix Coordinate Coordinate (CoefficientField m))ˣ :=
  FreeGroup.lift (fun rt => F4Chevalley.rootCurve rt.1 rt.2)

/-- Evaluation after exceptional root duality, squaring short-root parameters. -/
@[expose] noncomputable def twistedEval (m : ℕ) :
    FreeGroup (F4Chevalley.Root × CoefficientField m) →*
      (Matrix Coordinate Coordinate (CoefficientField m))ˣ :=
  FreeGroup.lift (fun rt => F4Chevalley.rootCurve
    (exceptionalRootPermutation rt.1) (exceptionalParameter rt.1 rt.2))

@[simp] theorem eval_of (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    eval m (FreeGroup.of (r, t)) = F4Chevalley.rootCurve r t := by
  simp only [eval, FreeGroup.lift_apply_of]

@[simp] theorem twistedEval_of (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    twistedEval m (FreeGroup.of (r, t)) =
      F4Chevalley.rootCurve (exceptionalRootPermutation r) (exceptionalParameter r t) := by
  simp only [twistedEval, FreeGroup.lift_apply_of]

/-- The word evaluation has exactly the actual root-generated matrix group as
its range. -/
theorem eval_range (m : ℕ) :
    (eval m).range = Subgroup.closure (Set.range
      (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve rt.1 rt.2)) :=
  FreeGroup.range_lift_eq_closure

/-- Exceptional substitution still evaluates to an element of the actual
root-generated matrix group. -/
theorem twistedEval_mem_closure (m : ℕ)
    (w : FreeGroup (F4Chevalley.Root × CoefficientField m)) :
    twistedEval m w ∈ Subgroup.closure (Set.range
      (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve rt.1 rt.2)) := by
  have h : (twistedEval m).range ≤ Subgroup.closure (Set.range
      (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve rt.1 rt.2)) := by
    apply FreeGroup.range_lift_le
    rintro _ ⟨⟨r, t⟩, rfl⟩
    exact Subgroup.subset_closure
      ⟨(exceptionalRootPermutation r, exceptionalParameter r t), rfl⟩
  exact h ⟨w, rfl⟩

/-- The concrete quotient-to-ideal matrix intertwines both evaluations on
every free word. -/
theorem eval_intertwines (m : ℕ)
    (w : FreeGroup (F4Chevalley.Root × CoefficientField m)) :
    quotientToIdeal * (eval m w : Matrix Coordinate Coordinate (CoefficientField m)) =
      (twistedEval m w : Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal :=
  lift_intertwines
    (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve rt.1 rt.2)
    (fun rt : F4Chevalley.Root × CoefficientField m => F4Chevalley.rootCurve
      (exceptionalRootPermutation rt.1) (exceptionalParameter rt.1 rt.2))
    quotientToIdeal (fun rt => intertwines_rootCurve m rt.1 rt.2) w

/-- Every relation among the concrete F4 matrices is preserved by exceptional
root substitution, for every Ree coefficient field including `m = 0`. -/
theorem twistedEval_eq_one_of_eval_eq_one (m : ℕ)
    (w : FreeGroup (F4Chevalley.Root × CoefficientField m))
    (hw : eval m w = 1) : twistedEval m w = 1 := by
  apply Faithfulness.eq_one_of_mul_quotientToIdeal_eq m (twistedEval m w)
    (twistedEval_mem_closure m w)
  have h := eval_intertwines m w
  rw [hw, Units.val_one, mul_one] at h
  exact h.symm

/-- The unconditional kernel inclusion permitting descent of exceptional root
substitution to the concrete root-generated F4 group. -/
theorem ker_eval_le_ker_twistedEval (m : ℕ) :
    (eval m).ker ≤ (twistedEval m).ker := by
  intro w hw
  exact twistedEval_eq_one_of_eval_eq_one m w hw

/-- Equal concrete matrix words have equal exceptional substitutions. -/
theorem twistedEval_eq_of_eval_eq (m : ℕ)
    {v w : FreeGroup (F4Chevalley.Root × CoefficientField m)}
    (h : eval m v = eval m w) : twistedEval m v = twistedEval m w := by
  apply inv_mul_eq_one.mp
  have hrel : eval m (v⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  simpa only [map_mul, map_inv] using twistedEval_eq_one_of_eval_eq_one m (v⁻¹ * w) hrel

end ReeF4.WordRelations
