module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Stem

/-!
# Exact arithmetic for the principal eleven-block ordering

The alternating inverse to line incidence computes prospective simple rows
from an ordinary-row path. The table is encoded over the integer span of
`1,c,d,a,ac,ad`, with multiplication specified by the fifth- and
nineteenth-root period relations. `tensorNumerator` is the prospective
reciprocity pairing, scaled by 175560 to remove every denominator.

These definitions assert no period identity, tensor positivity, or exhaustive
path classification. Those are separate proof obligations. The actual stem
is connected to this finite calculation in `Ordering.lean`.

The ordinary table is the ATLAS/GAP CTblLib J1 table (Thomas Breuer,
GPL-3.0-or-later); see `../../../Source.md` and its license. The modular
application is Janko, J. Algebra 3 (1966), 147–186, and Feit, Chapter VII.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

/-- The signs along a path oriented from its first endpoint. -/
@[expose] public def vertexSign : Fin 11 → ℤ := ![1,-1,1,-1,1,-1,1,-1,1,-1,1]

/-- The actual ordinary values at the unique eleven-singular class. -/
@[expose] public def ordinarySign : Fin 15 → ℤ :=
  ![1,1,1,-1,-1,0,0,0,-1,-1,-1,1,1,1,0]

/-- Recover the ten edges successively from the first ten vertex sums. -/
@[expose] public def edgeTerms {A : Type*} [Sub A] (v : Fin 11 → A) : Fin 10 → A :=
  let e0 := v 0
  let e1 := v 1 - e0
  let e2 := v 2 - e1
  let e3 := v 3 - e2
  let e4 := v 4 - e3
  let e5 := v 5 - e4
  let e6 := v 6 - e5
  let e7 := v 7 - e6
  let e8 := v 8 - e7
  let e9 := v 9 - e8
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- Numerical necessary conditions on a stem, including its last endpoint.
The positivity and endpoint equation are over integers, never modulo eleven. -/
public structure Admissible (r : Fin 11 → Fin 15) : Prop where
  injective : Function.Injective r
  first : r 0 = 0
  nonzero_defect : ∀ i, ¬ 11 ∣ ordinaryDegree (r i)
  alternating : ∀ i, ordinarySign (r i) = vertexSign i
  positive : ∀ i, 0 < edgeTerms (fun j => (ordinaryDegree (r j) : ℤ)) i
  last : edgeTerms (fun j => (ordinaryDegree (r j) : ℤ)) 9 = ordinaryDegree (r 10)

/-- Six integer coefficients in the ordered span `1,c,d,a,ac,ad`.
No assertion of linear independence is needed for the certificate. -/
public abbrev Coeff := Fin 6 → ℤ

/-- Constant coefficient vector. -/
@[expose] public def scalar (n : ℤ) : Coeff := ![n,0,0,0,0,0]

/-- Multiplication in the cubic span `1,c,d`, using
`c²=4-d`, `cd=-3-2c-d`, and `d²=5+c+d`. -/
@[expose] public def cubicMul (x y : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![x 0*y 0 + 4*x 1*y 1 - 3*(x 1*y 2 + x 2*y 1) + 5*x 2*y 2,
    x 0*y 1 + x 1*y 0 - 2*(x 1*y 2 + x 2*y 1) + x 2*y 2,
    x 0*y 2 + x 2*y 0 - x 1*y 1 - (x 1*y 2 + x 2*y 1) + x 2*y 2]

/-- Multiplication in the six-dimensional integer span, using `a²=1-a`.
The operation is explicit so its individual certificate evaluations reduce
in Lean's kernel. -/
@[expose] public def coeffMul (x y : Coeff) : Coeff :=
  let x₀ := ![x 0, x 1, x 2]
  let x₁ := ![x 3, x 4, x 5]
  let y₀ := ![y 0, y 1, y 2]
  let y₁ := ![y 3, y 4, y 5]
  let u := cubicMul x₀ y₀ + cubicMul x₁ y₁
  let v := cubicMul x₀ y₁ + cubicMul x₁ y₀ - cubicMul x₁ y₁
  ![u 0, u 1, u 2, v 0, v 1, v 2]

/-- Evaluate a coefficient vector at the literal periods from `ordinaryValue`. -/
@[expose] public noncomputable def evaluate (ζ₅ ζ₁₉ : ℂ) (x : Coeff) : ℂ :=
  let a := ζ₅ + ζ₅ ^ 4
  let c := ζ₁₉ + ζ₁₉ ^ 7 + ζ₁₉ ^ 8 + ζ₁₉ ^ 11 + ζ₁₉ ^ 12 + ζ₁₉ ^ 18
  let d := ζ₁₉ ^ 2 + ζ₁₉ ^ 3 + ζ₁₉ ^ 5 + ζ₁₉ ^ 14 + ζ₁₉ ^ 16 + ζ₁₉ ^ 17
  (x 0 : ℂ) + (x 1 : ℂ)*c + (x 2 : ℂ)*d + (x 3 : ℂ)*a +
    (x 4 : ℂ)*(a*c) + (x 5 : ℂ)*(a*d)

/-- The ordinary table in exact period coordinates. Constants are constant
basis vectors, not the constant functions on the six coordinate indices. -/
@[expose] public def coefficientTable : Fin 15 → Fin 15 → Coeff :=
  let a : Coeff := ![0,0,0,1,0,0]
  let b := -scalar 1 - a
  let c : Coeff := ![0,1,0,0,0,0]
  let d : Coeff := ![0,0,1,0,0,0]
  let e := -scalar 1 - c - d
  ![![scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1, scalar 1],
    ![scalar 56, scalar 0, scalar 2, -(2 • a), -(2 • b), scalar 0, scalar 0, scalar 0, scalar 0, scalar 1, a, b, scalar (-1), scalar (-1), scalar (-1)],
    ![scalar 56, scalar 0, scalar 2, -(2 • b), -(2 • a), scalar 0, scalar 0, scalar 0, scalar 0, scalar 1, b, a, scalar (-1), scalar (-1), scalar (-1)],
    ![scalar 76, scalar 4, scalar 1, scalar 1, scalar 1, scalar 1, scalar (-1), scalar (-1), scalar (-1), scalar (-1), scalar 1, scalar 1, scalar 0, scalar 0, scalar 0],
    ![scalar 76, scalar (-4), scalar 1, scalar 1, scalar 1, scalar (-1), scalar (-1), scalar 1, scalar 1, scalar (-1), scalar 1, scalar 1, scalar 0, scalar 0, scalar 0],
    ![scalar 77, scalar 5, scalar (-1), scalar 2, scalar 2, scalar (-1), scalar 0, scalar 0, scalar 0, scalar 0, scalar (-1), scalar (-1), scalar 1, scalar 1, scalar 1],
    ![scalar 77, scalar (-3), scalar 2, a, b, scalar 0, scalar 0, a, b, scalar 0, a, b, scalar 1, scalar 1, scalar 1],
    ![scalar 77, scalar (-3), scalar 2, b, a, scalar 0, scalar 0, b, a, scalar 0, b, a, scalar 1, scalar 1, scalar 1],
    ![scalar 120, scalar 0, scalar 0, scalar 0, scalar 0, scalar 0, scalar 1, scalar 0, scalar 0, scalar (-1), scalar 0, scalar 0, c, d, e],
    ![scalar 120, scalar 0, scalar 0, scalar 0, scalar 0, scalar 0, scalar 1, scalar 0, scalar 0, scalar (-1), scalar 0, scalar 0, e, c, d],
    ![scalar 120, scalar 0, scalar 0, scalar 0, scalar 0, scalar 0, scalar 1, scalar 0, scalar 0, scalar (-1), scalar 0, scalar 0, d, e, c],
    ![scalar 133, scalar 5, scalar 1, scalar (-2), scalar (-2), scalar (-1), scalar 0, scalar 0, scalar 0, scalar 1, scalar 1, scalar 1, scalar 0, scalar 0, scalar 0],
    ![scalar 133, scalar (-3), scalar (-2), -a, -b, scalar 0, scalar 0, a, b, scalar 1, -a, -b, scalar 0, scalar 0, scalar 0],
    ![scalar 133, scalar (-3), scalar (-2), -b, -a, scalar 0, scalar 0, b, a, scalar 1, -b, -a, scalar 0, scalar 0, scalar 0],
    ![scalar 209, scalar 1, scalar (-1), scalar (-1), scalar (-1), scalar 1, scalar (-1), scalar 1, scalar 1, scalar 0, scalar (-1), scalar (-1), scalar 0, scalar 0, scalar 0]]

/-- The reciprocity numerator in integer coordinates, using precisely the
regular columns and reciprocal centralizer weights from the source table. -/
@[expose] public def tensorNumerator (r : Fin 11 → Fin 15) (i j k : Fin 10) : Coeff :=
  ∑ t ∈ (Finset.univ.erase (9 : Fin 15)),
    (175560 / centralizerOrder t : ℕ) •
      coeffMul (coeffMul (edgeTerms (fun v => coefficientTable (r v) t) i)
        (edgeTerms (fun v => coefficientTable (r v) t) j))
        (coefficientTable (r k.castSucc) t + coefficientTable (r k.succ) t)

/-- The same pairing in the literal complex ordinary table, before any use
of root identities or exact arithmetic. -/
@[expose] public noncomputable def tableTensor (r : Fin 11 → Fin 15)
    (ζ₅ ζ₁₉ : ℂ) (i j k : Fin 10) : ℂ :=
  ∑ t ∈ (Finset.univ.erase (9 : Fin 15)),
    edgeTerms (fun v => ordinaryValue ζ₅ ζ₁₉ (r v) t) i *
      edgeTerms (fun v => ordinaryValue ζ₅ ζ₁₉ (r v) t) j *
        star (ordinaryValue ζ₅ ζ₁₉ (r k.castSucc) t +
          ordinaryValue ζ₅ ζ₁₉ (r k.succ) t) / (centralizerOrder t : ℂ)

/-- Constant integer coordinates evaluate to that same integer. -/
public theorem evaluate_scalar (ζ₅ ζ₁₉ : ℂ) (n : ℤ) :
    evaluate ζ₅ ζ₁₉ (scalar n) = n := by
  simp [evaluate, scalar]

/-- Successive subtraction recovers every edge of a line. -/
public theorem edgeTerms_lineIncidence {A : Type*} [AddCommGroup A] (v : Fin 10 → A) :
    edgeTerms (lineIncidence v) = v := by
  funext i
  fin_cases i <;> simp [edgeTerms, lineIncidence, add_sub_cancel_left]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering
