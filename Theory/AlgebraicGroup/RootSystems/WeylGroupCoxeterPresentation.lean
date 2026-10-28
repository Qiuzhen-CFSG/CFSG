module

public import Theory.AlgebraicGroup.RootSystems.Deletion

/-! The Coxeter presentation of a reduced crystallographic Weyl group. -/

namespace Theory.AlgebraicGroup

/-- The simple reflections present the Weyl group as the Coxeter group whose
matrix records the exact orders of their pairwise products.

This is GLS3, Theorem 1.8.3(i). -/
public theorem _root_.RootPairing.Base.weylGroup_coxeterPresentation
    {I M N : Type*} [Finite I]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing I ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) :
    ∃ C : CoxeterMatrix b.support, ∃ cs : CoxeterSystem C P.weylGroup,
      (∀ i j : b.support,
        C i j = orderOf (b.simpleReflection i * b.simpleReflection j)) ∧
      (∀ i : b.support,
        CoxeterSystem.simple cs i = b.simpleReflection i) := by
  apply weylGroup_coxeterPresentation_of_deletion b
  intro C hC l hl
  exact b.wordProd_one_reflTransGen_nil C hC l hl

end Theory.AlgebraicGroup
