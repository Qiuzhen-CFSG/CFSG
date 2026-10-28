module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Factors

/-!
# Soundness of the full ambient factor checks

Checking `rep j * gen a = factor * rep (next j)` avoids numerically inverting
representatives. After comparison on every ambient point, permutation
extensionality and cancellation give the literal Schreier factorization.
Signed factors belong to the specified next subgroup by construction.
No inverse-action-on-labels premise or earlier stabilizer reduction is used.
Source: the retained `factors.json.gz`, ATLAS F24G1-p306936B0, GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

def leftWord (i a : Fin 2) (j : Fin (size i)) : List Letter :=
  representativeWord i j ++ [(currentIndex i a, true)]

def rightWord (i a : Fin 2) (j : Fin (size i)) : List Letter :=
  factorWord i (factors i a j) ++ representativeWord i (next i a j)

def pointCheck (f : NumericalMaps) (i a : Fin 2) (j : Fin (size i)) (x : Nat) : Bool :=
  evaluateNat f (leftWord i a j) (x % 306936) ==
    evaluateNat f (rightWord i a j) (x % 306936)

theorem leftWord_eq (i a : Fin 2) (j : Fin (size i)) :
    evaluate (leftWord i a j) = representative i j * gen i a := by
  rw [leftWord, evaluate_append, representativeWord_eq]
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, signed, ite_true, currentIndex_eq]

theorem rightWord_eq (i a : Fin 2) (j : Fin (size i)) :
    evaluate (rightWord i a j) =
      evaluate (factorWord i (factors i a j)) * representative i (next i a j) := by
  rw [rightWord, evaluate_append, representativeWord_eq]

/-- Full-point numerical checks yield a literal ambient permutation identity. -/
theorem schreier_eq_of_pointChecks (f : NumericalMaps) (hf : MapsCorrect f)
    (i a : Fin 2) (j : Fin (size i))
    (h : ∀ x : Fin 306936, pointCheck f i a j x.val = true) :
    schreier i a j = evaluate (factorWord i (factors i a j)) := by
  have he : evaluate (leftWord i a j) = evaluate (rightWord i a j) := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    have hx := h x
    simp only [pointCheck, Nat.mod_eq_of_lt x.isLt, beq_iff_eq,
      evaluateNat_correct f hf] at hx
    exact hx
  rw [leftWord_eq, rightWord_eq] at he
  rw [schreier, he, mul_assoc, mul_inv_cancel, mul_one]

theorem edge_mem_of_pointChecks (f : NumericalMaps) (hf : MapsCorrect f)
    (i a : Fin 2) (j : Fin (size i))
    (h : ∀ x : Fin 306936, pointCheck f i a j x.val = true) :
    schreier i a j ∈ stage (i.natAdd 2).succ := by
  rw [schreier_eq_of_pointChecks f hf i a j h]
  exact factorWord_mem i _

/-- A finite arithmetic obligation; the full degree is essential. -/
def StageChecks (f : NumericalMaps) (i : Fin 2) : Prop :=
  ∀ (a : Fin 2) (j : Fin (size i)), ¬ IsTree i a j →
    ∀ x : Fin 306936, pointCheck f i a j x.val = true

theorem nonTreeEdges_of_checks (f : NumericalMaps) (hf : MapsCorrect f)
    (h₀ : StageChecks f 0) (h₁ : StageChecks f 1) : NonTreeEdges := by
  intro i a j hj
  apply edge_mem_of_pointChecks f hf
  fin_cases i
  · exact h₀ a j hj
  · exact h₁ a j hj

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges
