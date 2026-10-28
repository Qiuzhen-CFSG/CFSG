module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.StemReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.PeriodArithmetic.Periods

/-!
# Sound evaluation of the exact principal-path tensor arithmetic

Evaluation at the literal fifth- and nineteenth-root periods preserves the
published coefficient multiplication and agrees with every ordinary-table
entry. All these values are real. Thus the integer numerator, which omits
conjugation, evaluates to 175560 times the reciprocal-centralizer pairing
on precisely the columns other than nine. This holds for every row sequence.

The final theorem applies this identity to a genuine `RealStem`, using its
ordinary data and the recurrence theorem in `StemReduction`. Existence of the
stem and tensor positivity are separate source obligations, not assumptions
needed for the arithmetic identity proved here.

The table remains the ATLAS/GAP CTblLib J1 table (Thomas Breuer,
GPL-3.0-or-later); see `ModularCharacters/Source.md` and
`PathRealization/Source.md`. Source application: Janko, J. Algebra 3 (1966),
147–186, and Feit, Chapter VII.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

private def cubicEval (c d : ℂ) (x : Fin 3 → ℤ) : ℂ :=
  (x 0 : ℂ) + (x 1 : ℂ)*c + (x 2 : ℂ)*d

private theorem cubicEval_add (c d : ℂ) (x y : Fin 3 → ℤ) :
    cubicEval c d (x + y) = cubicEval c d x + cubicEval c d y := by
  simp only [cubicEval, Pi.add_apply, Int.cast_add]
  ring

private theorem cubicEval_sub (c d : ℂ) (x y : Fin 3 → ℤ) :
    cubicEval c d (x - y) = cubicEval c d x - cubicEval c d y := by
  simp only [cubicEval, Pi.sub_apply, Int.cast_sub]
  ring

private theorem cubicEval_mul (c d : ℂ)
    (hc : c ^ 2 = 4 - d) (hcd : c*d = -3 - 2*c - d) (hd : d ^ 2 = 5 + c + d)
    (x y : Fin 3 → ℤ) : cubicEval c d (cubicMul x y) = cubicEval c d x * cubicEval c d y := by
  simp [cubicEval, cubicMul]
  linear_combination -((x 1 : ℂ) * (y 1 : ℂ)) * hc -
    ((x 1 : ℂ) * (y 2 : ℂ) + (x 2 : ℂ) * (y 1 : ℂ)) * hcd -
    ((x 2 : ℂ) * (y 2 : ℂ)) * hd

private def evalAt (a c d : ℂ) (x : Coeff) : ℂ :=
  (x 0 : ℂ) + (x 1 : ℂ)*c + (x 2 : ℂ)*d + (x 3 : ℂ)*a +
    (x 4 : ℂ)*(a*c) + (x 5 : ℂ)*(a*d)

private theorem evalAt_blocks (a c d : ℂ) (x y : Fin 3 → ℤ) :
    evalAt a c d ![x 0, x 1, x 2, y 0, y 1, y 2] =
      cubicEval c d x + a*cubicEval c d y := by
  simp [evalAt, cubicEval]
  ring

private theorem evalAt_split (a c d : ℂ) (x : Coeff) :
    evalAt a c d x = cubicEval c d ![x 0, x 1, x 2] +
      a*cubicEval c d ![x 3, x 4, x 5] := by
  simp [evalAt, cubicEval]
  ring

private theorem evalAt_mul (a c d : ℂ) (ha : a ^ 2 = 1 - a)
    (hc : c ^ 2 = 4 - d) (hcd : c*d = -3 - 2*c - d) (hd : d ^ 2 = 5 + c + d)
    (x y : Coeff) : evalAt a c d (coeffMul x y) = evalAt a c d x * evalAt a c d y := by
  unfold coeffMul
  rw [evalAt_blocks]
  simp only [cubicEval_add, cubicEval_sub, cubicEval_mul c d hc hcd hd]
  rw [evalAt_split a c d x, evalAt_split a c d y]
  linear_combination -(cubicEval c d ![x 3, x 4, x 5] *
    cubicEval c d ![y 3, y 4, y 5]) * ha


private noncomputable def evaluateHom (ζ₅ ζ₁₉ : ℂ) : Coeff →+ ℂ where
  toFun := evaluate ζ₅ ζ₁₉
  map_zero' := by simp [evaluate]
  map_add' := by
    intro x y
    simp only [evaluate, Pi.add_apply, Int.cast_add]
    ring

/-- Evaluation preserves addition of coefficient vectors. -/
public theorem evaluate_add (ζ₅ ζ₁₉ : ℂ) (x y : Coeff) :
    evaluate ζ₅ ζ₁₉ (x + y) = evaluate ζ₅ ζ₁₉ x + evaluate ζ₅ ζ₁₉ y :=
  (evaluateHom ζ₅ ζ₁₉).map_add x y

/-- Evaluation preserves subtraction of coefficient vectors. -/
public theorem evaluate_sub (ζ₅ ζ₁₉ : ℂ) (x y : Coeff) :
    evaluate ζ₅ ζ₁₉ (x - y) = evaluate ζ₅ ζ₁₉ x - evaluate ζ₅ ζ₁₉ y :=
  map_sub (evaluateHom ζ₅ ζ₁₉) x y

/-- Evaluation preserves negation of coefficient vectors. -/
public theorem evaluate_neg (ζ₅ ζ₁₉ : ℂ) (x : Coeff) :
    evaluate ζ₅ ζ₁₉ (-x) = -evaluate ζ₅ ζ₁₉ x :=
  map_neg (evaluateHom ζ₅ ζ₁₉) x

/-- Natural scalar weights evaluate to multiplication by the same complex integer. -/
public theorem evaluate_nsmul (ζ₅ ζ₁₉ : ℂ) (n : ℕ) (x : Coeff) :
    evaluate ζ₅ ζ₁₉ (n • x) = (n : ℂ) * evaluate ζ₅ ζ₁₉ x := by
  exact (map_nsmul (evaluateHom ζ₅ ζ₁₉) n x).trans (nsmul_eq_mul n _)

/-- Evaluation commutes with finite sums of coefficient vectors. -/
public theorem evaluate_sum {ι : Type*} (ζ₅ ζ₁₉ : ℂ) (s : Finset ι) (x : ι → Coeff) :
    evaluate ζ₅ ζ₁₉ (∑ i ∈ s, x i) = ∑ i ∈ s, evaluate ζ₅ ζ₁₉ (x i) :=
  map_sum (evaluateHom ζ₅ ζ₁₉) x s

/-- The published coefficient multiplication evaluates to complex multiplication. -/
public theorem evaluate_coeffMul {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) (x y : Coeff) :
    evaluate ζ₅ ζ₁₉ (coeffMul x y) = evaluate ζ₅ ζ₁₉ x * evaluate ζ₅ ζ₁₉ y := by
  obtain ⟨ha, _, _, _⟩ := fifth_period_arithmetic h₅
  obtain ⟨hc, hcd, hd, _, _, _, _⟩ := nineteenth_period_arithmetic h₁₉
  exact evalAt_mul _ _ _ ha hc hcd hd x y

/-- Every integral combination of the six period monomials is fixed by conjugation. -/
public theorem star_evaluate {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) (x : Coeff) :
    star (evaluate ζ₅ ζ₁₉ x) = evaluate ζ₅ ζ₁₉ x := by
  obtain ⟨_, _, ha, _⟩ := fifth_period_arithmetic h₅
  obtain ⟨_, _, _, _, hc, hd, _⟩ := nineteenth_period_arithmetic h₁₉
  simp only [evaluate, star_add, star_mul, star_intCast, ha, hc, hd]
  ac_rfl

private theorem map_vecCons {α β : Type*} {n : ℕ} (f : α → β) (x : α) (v : Fin n → α) :
    f ∘ Matrix.vecCons x v = Matrix.vecCons (f x) (f ∘ v) := Fin.comp_cons f x v

private theorem map_vecEmpty {α β : Type*} (f : α → β) :
    f ∘ (![] : Fin 0 → α) = ![] := Subsingleton.elim _ _

/-- The exact coordinate table evaluates to the literal ordinary table. -/
public theorem evaluate_coefficientTable {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) (i j : Fin 15) :
    evaluate ζ₅ ζ₁₉ (coefficientTable i j) = ordinaryValue ζ₅ ζ₁₉ i j := by
  obtain ⟨_, hb, _, _⟩ := fifth_period_arithmetic h₅
  obtain ⟨_, _, _, he, _, _, _⟩ := nineteenth_period_arithmetic h₁₉
  have ha : evaluate ζ₅ ζ₁₉ ![0,0,0,1,0,0] = ζ₅ + ζ₅ ^ 4 := by simp [evaluate]
  have hc : evaluate ζ₅ ζ₁₉ ![0,1,0,0,0,0] =
      ζ₁₉ + ζ₁₉ ^ 7 + ζ₁₉ ^ 8 + ζ₁₉ ^ 11 + ζ₁₉ ^ 12 + ζ₁₉ ^ 18 := by simp [evaluate]
  have hd : evaluate ζ₅ ζ₁₉ ![0,0,1,0,0,0] =
      ζ₁₉ ^ 2 + ζ₁₉ ^ 3 + ζ₁₉ ^ 5 + ζ₁₉ ^ 14 + ζ₁₉ ^ 16 + ζ₁₉ ^ 17 := by simp [evaluate]
  apply congrFun (show evaluate ζ₅ ζ₁₉ ∘ coefficientTable i = ordinaryValue ζ₅ ζ₁₉ i from ?_) j
  dsimp only [ordinaryValue]
  rw [hb, he]
  fin_cases i <;>
    simp only [coefficientTable, Matrix.cons_val_zero', Matrix.cons_val_succ', map_vecCons, map_vecEmpty,
      evaluate_sub, evaluate_neg, evaluate_nsmul, evaluate_scalar, ha, hc, hd] <;>
    norm_num [neg_mul]

/-- Evaluation commutes with the successive subtraction defining path edges. -/
public theorem evaluate_edgeTerms (ζ₅ ζ₁₉ : ℂ) (v : Fin 11 → Coeff) (i : Fin 10) :
    evaluate ζ₅ ζ₁₉ (edgeTerms v i) =
      edgeTerms (fun j => evaluate ζ₅ ζ₁₉ (v j)) i := by
  fin_cases i <;> simp [edgeTerms, evaluate_sub]

/-- Every entry of the literal ordinary table is real. This justifies the
absence of conjugation in the integer tensor numerator. -/
public theorem star_ordinaryValue {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19) (i j : Fin 15) :
    star (ordinaryValue ζ₅ ζ₁₉ i j) = ordinaryValue ζ₅ ζ₁₉ i j := by
  rw [← evaluate_coefficientTable h₅ h₁₉]
  exact star_evaluate h₅ h₁₉ _

/-- Each published integer weight is exactly 175560 times the reciprocal
centralizer order. The tensor sum itself omits precisely column nine. -/
public theorem centralizer_weight (t : Fin 15) :
    ((175560 / centralizerOrder t : ℕ) : ℂ) = 175560 / (centralizerOrder t : ℂ) := by
  fin_cases t <;> norm_num [centralizerOrder]

/-- Primitive-root interpretation of the exact integer tensor numerator.
No admissibility condition on the row sequence is needed. -/
public theorem evaluate_tensorNumerator {ζ₅ ζ₁₉ : ℂ}
    (h₅ : IsPrimitiveRoot ζ₅ 5) (h₁₉ : IsPrimitiveRoot ζ₁₉ 19)
    (r : Fin 11 → Fin 15) (i j k : Fin 10) :
    evaluate ζ₅ ζ₁₉ (tensorNumerator r i j k) =
      (175560 : ℂ) * tableTensor r ζ₅ ζ₁₉ i j k := by
  unfold tensorNumerator tableTensor
  rw [evaluate_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [evaluate_nsmul, evaluate_coeffMul h₅ h₁₉, evaluate_add,
    evaluate_edgeTerms]
  simp_rw [evaluate_coefficientTable h₅ h₁₉]
  rw [star_add, star_ordinaryValue h₅ h₁₉, star_ordinaryValue h₅ h₁₉,
    centralizer_weight]
  ring

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

/-- For a genuine real stem, the integer numerator evaluates to the actual
reciprocity pairing scaled by the source group order. Primitive-root premises
come from its ordinary data; the stem construction remains an explicit input. -/
public theorem RealStem.evaluate_tensorNumerator {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) (i j k : Fin 10) :
    PathOrdering.evaluate d.rootFive d.rootNineteen
      (PathOrdering.tensorNumerator s.row i j k) =
        (175560 : ℂ) * s.tensorCoefficient i j k := by
  rw [s.tensorCoefficient_eq_tableTensor]
  exact PathOrdering.evaluate_tensorNumerator d.rootFive_primitive
    d.rootNineteen_primitive s.row i j k

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
