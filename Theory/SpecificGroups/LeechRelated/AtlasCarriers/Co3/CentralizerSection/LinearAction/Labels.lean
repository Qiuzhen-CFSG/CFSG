module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearAction.Refinements
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.PointTables

/-!
# The exact 36-point marking of the even quadratic refinements

The bit parameters are the literal candidates in `source/linear-witnesses.json`
one directory above: bits 0,1,2 are the first hyperbolic half, and bits 3,4,5
are the second. A checked left inverse proves the labels distinct; the proved
count of even refinements proves the enumeration exhaustive.

For each of the three fixed matrices and each of the 36 labels, we check six
basis values. Reconstruction of refinements then proves the full action
identity with the unchanged `Tables.pointGenerator`. Checking the forward
matrix on a target form also fixes the inverse-substitution convention.
This is the marked comparison needed for GLS3 Table 5.3j and
Aschbacher--Smith A.2.19, printed pp.40–41.
-/

@[expose] public section
noncomputable section
namespace Sporadic.LeechRelated.Co3.CentralizerSection.LinearAction
open LinearData (K Index Sp)

/-- Point-to-parameter codes, in the original 36-point order. -/
def pointCode (i : Fin 36) : ℕ :=
  let n := i.val
  (if n < 18 then (if n < 9 then (if n < 4 then (if n < 2 then (if n < 1 then 33 else 34) else (if n < 3 then 28 else 32)) else (if n < 6 then (if n < 5 then 31 else 16) else (if n < 7 then 55 else (if n < 8 then 62 else 12)))) else (if n < 13 then (if n < 11 then (if n < 10 then 0 else 49) else (if n < 12 then 42 else 14)) else (if n < 15 then (if n < 14 then 3 else 17) else (if n < 16 then 47 else (if n < 17 then 27 else 59))))) else (if n < 27 then (if n < 22 then (if n < 20 then (if n < 19 then 48 else 1) else (if n < 21 then 54 else 40)) else (if n < 24 then (if n < 23 then 2 else 21) else (if n < 25 then 4 else (if n < 26 then 45 else 56)))) else (if n < 31 then (if n < 29 then (if n < 28 then 5 else 7) else (if n < 30 then 6 else 24)) else (if n < 33 then (if n < 32 then 61 else 20) else (if n < 34 then 10 else (if n < 35 then 8 else 35))))))

/-- Decode the six binary coordinates in the fixed hyperbolic basis. -/
def decode (n : ℕ) : V :=
  Sum.elim ![if n.testBit 0 then 1 else 0, if n.testBit 1 then 1 else 0,
    if n.testBit 2 then 1 else 0]
    ![if n.testBit 3 then 1 else 0, if n.testBit 4 then 1 else 0,
    if n.testBit 5 then 1 else 0]

def pointParameter (i : Fin 36) : V := decode (pointCode i)

private def indexOfCode (n : ℕ) : Fin 36 :=
  (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 9 else 19) else (if n < 3 then 22 else 13)) else (if n < 6 then (if n < 5 then 24 else 27) else (if n < 7 then 29 else 28))) else (if n < 12 then (if n < 10 then (if n < 9 then 34 else 9) else (if n < 11 then 33 else 9)) else (if n < 14 then (if n < 13 then 8 else 9) else (if n < 15 then 12 else 9)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 5 else 14) else (if n < 19 then 9 else 9)) else (if n < 22 then (if n < 21 then 32 else 23) else (if n < 23 then 9 else 9))) else (if n < 28 then (if n < 26 then (if n < 25 then 30 else 9) else (if n < 27 then 9 else 16)) else (if n < 30 then (if n < 29 then 2 else 9) else (if n < 31 then 9 else 4))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 3 else 0) else (if n < 35 then 1 else 35)) else (if n < 38 then (if n < 37 then 9 else 9) else (if n < 39 then 9 else 9))) else (if n < 44 then (if n < 42 then (if n < 41 then 21 else 9) else (if n < 43 then 11 else 9)) else (if n < 46 then (if n < 45 then 9 else 25) else (if n < 47 then 9 else 15)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 18 else 10) else (if n < 51 then 9 else 9)) else (if n < 54 then (if n < 53 then 9 else 9) else (if n < 55 then 20 else 6))) else (if n < 60 then (if n < 58 then (if n < 57 then 26 else 9) else (if n < 59 then 9 else 17)) else (if n < 62 then (if n < 61 then 9 else 31) else (if n < 63 then 7 else 9))))))

private def indexOfParameter (x : V) : Fin 36 :=
  indexOfCode ((x (.inl 0)).val + 2*(x (.inl 1)).val + 4*(x (.inl 2)).val +
    8*(x (.inr 0)).val + 16*(x (.inr 1)).val + 32*(x (.inr 2)).val)

set_option maxRecDepth 10000 in
theorem pointParameter_even : ∀ i, q₀ (pointParameter i) = 0 := by
  apply Tables.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem indexOfParameter_point : ∀ i, indexOfParameter (pointParameter i) = i := by
  apply Tables.allFin
  decide +kernel

theorem pointParameter_injective : Function.Injective pointParameter :=
  Function.LeftInverse.injective indexOfParameter_point

def pointForm (i : Fin 36) : EvenRefinement :=
  evenForm (pointParameter i) (pointParameter_even i)

theorem pointForm_injective : Function.Injective pointForm := by
  intro i j h
  apply pointParameter_injective
  have h' := congrArg (fun Q : EvenRefinement => parameterOf Q.val) h
  change parameterOf (refinementOf (pointParameter i)) =
    parameterOf (refinementOf (pointParameter j)) at h'
  simpa only [parameter_refinement] using h'

/-- The labels exhaust all even refinements of the actual alternating form. -/
def pointFormEquiv : Fin 36 ≃ EvenRefinement :=
  Equiv.ofBijective pointForm ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨pointForm_injective, by rw [card_evenRefinement]; simp⟩)

@[simp] theorem pointFormEquiv_apply (i : Fin 36) : pointFormEquiv i = pointForm i := rfl

/-- Every parameter with even base quadratic value occurs in the supplied table. -/
theorem pointParameter_exhaustive (a : V) (ha : q₀ a = 0) :
    ∃ i, pointParameter i = a := by
  obtain ⟨i, hi⟩ := pointFormEquiv.surjective (evenForm a ha)
  refine ⟨i, ?_⟩
  have h := congrArg (fun Q : EvenRefinement => parameterOf Q.val) hi
  change parameterOf (refinementOf (pointParameter i)) = parameterOf (refinementOf a) at h
  simpa only [parameter_refinement] using h

set_option maxRecDepth 10000 in
/-- The finite certificate compares actual matrix columns and actual point tables. -/
theorem generator_basis_check : ∀ i : Fin 3, ∀ j : Fin 36, ∀ s : Index,
    (refinementOf (pointParameter (Tables.pointGenerator i j))).val
      (fun t => LinearData.matrix i t s) =
    (refinementOf (pointParameter j)).val (Pi.single s 1) := by
  apply Tables.allFin
  decide +kernel


/-- Agreement as quadratic forms, hence at every vector, in the prescribed marking. -/
theorem generator_pointForm (i : Fin 3) (j : Fin 36) :
    LinearData.generator i • pointForm j = pointForm (Tables.pointGenerator i j) := by
  suffices h : (LinearData.generator i)⁻¹ • pointForm (Tables.pointGenerator i j) =
      pointForm j from (inv_smul_eq_iff.mp h).symm
  apply Subtype.ext
  apply refinementEquiv.symm.injective
  change parameterOf _ = parameterOf _
  funext s
  rcases s with k | k
  · change (refinementOf (pointParameter (Tables.pointGenerator i j))).val
      (((LinearData.generator i)⁻¹)⁻¹ • f k) =
      (refinementOf (pointParameter j)).val (f k)
    rw [inv_inv]
    simpa only [Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec,
      LinearData.generator, f, Matrix.mulVec_single_one, Matrix.col_apply'] using
      generator_basis_check i j (.inr k)
  · change (refinementOf (pointParameter (Tables.pointGenerator i j))).val
      (((LinearData.generator i)⁻¹)⁻¹ • e k) =
      (refinementOf (pointParameter j)).val (e k)
    rw [inv_inv]
    simpa only [Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec,
      LinearData.generator, e, Matrix.mulVec_single_one, Matrix.col_apply'] using
      generator_basis_check i j (.inl k)

end Sporadic.LeechRelated.Co3.CentralizerSection.LinearAction
