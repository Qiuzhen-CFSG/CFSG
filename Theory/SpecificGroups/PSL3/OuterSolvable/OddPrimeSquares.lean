module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicDiagonal
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Outer squares of PSL₃ over prime fields

Every automorphism is linear conjugation, possibly followed by inverse
transpose. The field part is trivial, and inverse transpose normalizes
linear conjugations and has square one. Consequently every outer square
belongs to the actual cyclic diagonal image.

The inverse-transpose calculation generalizes the existing proof in
`Theory/SpecificGroups/PSL3/SevenAction/NormalForm.lean` to every field.
Source: GLS3, Theorem 2.5.12(a,c,e,i) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open scoped MatrixGroups
open Subgroup
namespace Matrix.PSL3.OuterSolvable.OddPrimeSquares
variable {F : Type*} [Field F]

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL(3,F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem graph_linearConj (g : GL (Fin 3) F) :
    graph F * linearConj F g = linearConj F (inverseTransposeGL g) * graph F := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  change QuotientGroup.mk (graphSL F (linearConjSL F g x)) =
    QuotientGroup.mk (linearConjSL F (inverseTransposeGL g) (graphSL F x))
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
    linearConjSL_toGL, graphSL_toGL]

/-- Over an odd prime field, every automorphism square is induced by GL₃. -/
theorem square_mem_innerDiagonal [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) (a : MulAut PSL(3,F)) :
    a ^ 2 ∈ innerDiagonal F := by
  have hfield (σ : F ≃+* F) : σ = 1 := FiniteField.ringAut_eq_one_of_card_prime hp hF σ
  have hc := standard_eq_top_of_odd_prime_card F hns hp ho hF
  obtain ⟨g, σ, ha⟩ := CartanActions.NormalizerForm.standard_factorization F
    (by intro σ m; rw [hfield σ, map_one, one_mul, mul_one]; rfl)
    (fun g => ⟨inverseTransposeGL g, graph_linearConj g⟩)
    (by intro σ; rw [hfield σ, map_one]; exact Commute.one_left _)
    a (hc ▸ mem_top a)
  simp only [hfield σ, map_one, mul_one] at ha
  rcases ha with rfl | rfl
  · exact ⟨g ^ 2, map_pow _ _ _⟩
  · refine ⟨g * inverseTransposeGL g, ?_⟩
    symm
    calc
      (linearConj F g * graph F) ^ 2 =
          linearConj F g * (graph F * linearConj F g) * graph F := by
            simp only [pow_two, mul_assoc]
      _ = (linearConj F g * linearConj F (inverseTransposeGL g)) * (graph F * graph F) := by
        rw [graph_linearConj]
        group
      _ = linearConj F (g * inverseTransposeGL g) := by
        rw [← pow_two, graph_sq, mul_one, ← map_mul]

/-- Every square in the actual outer quotient lies in its cyclic diagonal subgroup. -/
theorem outer_square_mem [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) (a : MulAut PSL(3,F)) :
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) a) ^ 2 ∈ innerDiagonalOuter F := by
  obtain ⟨g, hg⟩ := square_mem_innerDiagonal hns hp ho hF a
  refine ⟨g, ?_⟩
  change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g) = _
  rw [hg, map_pow]

end Matrix.PSL3.OuterSolvable.OddPrimeSquares
