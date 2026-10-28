module

public import Theory.Representation.FirstCohomologySymplecticFour.Generation
public import Theory.Representation.FirstCohomologySymplecticFour.Quadratic

/-!
# Quadratic cocycle values on the eight symplectic root families

The row-quadratic defect is nonzero only on the four long-root families. Its
coordinate formula below provides the comparison term for the local cocycle
calculation. The matrices are the elementary type-C₂ matrices from
`Generation`, rather than an algebraic-group root API.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408.
-/

@[expose] public section

open Matrix
namespace Representation.OneCohomology.SymplecticFour

variable {K : Type*} [Field K] [CharP K 2]

/-- The row-quadratic defects of the eight standard root matrices. -/
def rootQuadraticValue (r : Fin 8) (t : K) : (Fin 2 ⊕ Fin 2) → K :=
  ![Sum.elim ![t, 0] ![0, 0], Sum.elim ![0, 0] ![t, 0],
    Sum.elim ![0, t] ![0, 0], Sum.elim ![0, 0] ![0, t],
    (0 : (Fin 2 ⊕ Fin 2) → K), 0, 0, 0] r

lemma rootQuadraticValue_eq (r : Fin 8) (t : K) (i : Fin 2 ⊕ Fin 2) :
    rowQuadratic ((rootElement r t).val i) = rootQuadraticValue r t i := by
  fin_cases r <;> rcases i with i | i <;> fin_cases i <;>
    simp [rootQuadraticValue, rootElement, rootMatrix, rowQuadratic,
      Matrix.fromBlocks, Matrix.single, Matrix.sub_apply,
      Matrix.add_apply, CharTwo.neg_eq]

variable [Finite K]

/-- The quadratic cocycle on a root family, in coordinates. -/
lemma quadraticCocycle_rootElement (r : Fin 8) (t : K) :
    (quadraticCocycle (K := K)).val (rootElement r t) =
      (fun i => (frobeniusEquiv K 2).symm (rootQuadraticValue r t i)) := by
  funext i
  change (frobeniusEquiv K 2).symm (rowQuadratic ((rootElement r t).val i)) = _
  exact congrArg (frobeniusEquiv K 2).symm (rootQuadraticValue_eq r t i)

end Representation.OneCohomology.SymplecticFour
