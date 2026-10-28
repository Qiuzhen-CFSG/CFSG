module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer.DiagonalDetection
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer.OperatorComparison

/-!
# The centralizer of the degree-one root operators in the full linear Levi

Four actual degree-one root operators force a degree-preserving matrix to have
two diagonal values. The full Levi fixes the first Cartan vector, including its
complementary torus, so the first value is one. Determinant one and the absence
of nontrivial cube roots of unity in the Ree coefficient field force the second
value to be one as well. Thus the common centralizer in the full Levi is trivial.

The comparison with the actual operators uses integral simple-root columns and
the proved characteristic-two invariance under a change of root route. It
works directly in the faithful matrix model, retaining the full complementary
torus. Fixed-root spanning is independent of this calculation.

Source: the root-defined Levi and centralizer assertions of GLS3, Theorem
2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection
open Theory.AlgebraicGroup Parabolics
open ReeF4.Cartan.FieldSeparation.TraceValues RootCentralizer

/-- Centralizing the degree-one operators forces an element of the actual full
linear Levi to be the identity. -/
theorem fullLevi_eq_one_of_commute_rootOperators (m : ℕ)
    (l : Model m) (hl : l ∈ fullLevi m)
    (hc : ∀ r : F4Chevalley.Root, rootDegree r = 1 →
      Commute (modelMatrix m l) (rootOperator m r)) : l = 1 := by
  let A := reindex (modelMatrix m l)
  have hd : ∀ i j, degree i ≠ degree j → A i j = 0 := by
    intro i j hij
    exact fullLevi_preservesDegree l hl (basisEquiv i) (basisEquiv j)
      (by simpa only [← degree_eq_basisDegree] using hij)
  have hcomm : ∀ k : Fin 4, Commute A (testOperator k) := by
    intro k
    have he := congrArg reindex (hc (testRoot k) (testRoot_degree k)).eq
    change reindex (modelMatrix m l) * testOperator k =
      testOperator k * reindex (modelMatrix m l)
    simpa only [map_mul, rootOperator_testRoot] using he
  exact fullLevi_eq_one_of_diagonalShape m l hl (A 0 0) (A 15 15)
    (eq_diagonalShape_of_commute A hd hcomm)

set_option linter.unusedVariables false in
/-- The requested torus detection for the full fixed Levi, retaining the full
complementary torus in its definition. The stronger identity theorem also
applies when `m = 0`, so the source's lower bound is not needed here. -/
theorem fullLevi_mem_fixedTorus_of_commute_rootOperators (m : ℕ) (hm : 1 ≤ m)
    (l : Model m) (hl : l ∈ fullLevi m)
    (hc : ∀ r : F4Chevalley.Root, rootDegree r = 1 →
      Commute (modelMatrix m l) (rootOperator m r)) : l ∈ fixedTorus m := by
  rw [fullLevi_eq_one_of_commute_rootOperators m l hl hc]
  exact (fixedTorus m).one_mem

end ReeF4.SectionGeometry.LinearRadical.LeviDetection
