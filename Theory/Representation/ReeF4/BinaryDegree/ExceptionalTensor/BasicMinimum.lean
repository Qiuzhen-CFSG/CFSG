module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode

/-!
# The exceptional basic F4 minimum

The source basic weights have short-simple coefficients `(0,0)`, `(1,0)`,
`(0,1)`, and `(1,1)`. Every nontrivial rational irreducible factor with one
of these highest weights has dimension at least 26 over the algebraic
closure of a finite field of characteristic two.

The zero highest weight gives trivial action. For the two middle-node cases,
26 distinct Weyl weights give the bound. In the end-node case `(0,1)`, the
24 nonzero Weyl weights and two independent zero-weight vectors obtained
from the short A2 subsystem give 26 dimensions. The final theorem discharges
all three premises of the general case-assembly lemma below.

Source: GLS3, Definition 2.8.1(b), Chapter 1, Section 1.14, and the defining
characteristic representation bound used on printed p.356 of Quasithin.
-/

public section

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u

/-- Assemble the minimum from the zero, middle-node, and end-node cases. -/
theorem basicFactorMinimum_of_highestWeight_bounds
    {F : Type u} [Field F] [IsAlgClosed F]
    (hzero : ∀ B : AlgebraicFactor F,
      B.HasBasicHighestWeight (0, 0) → ¬ B.IsNontrivial)
    (hmiddle : ∀ (B : AlgebraicFactor F) (b : Fin 2),
      B.HasBasicHighestWeight (1, b) → 26 ≤ Module.finrank F B.Space)
    (hend : ∀ B : AlgebraicFactor F,
      B.HasBasicHighestWeight (0, 1) → 26 ≤ Module.finrank F B.Space) :
    BasicFactorMinimum F 26 := by
  intro B hB hnontrivial
  obtain ⟨⟨a, b⟩, hweight⟩ := B.isExceptionalBasic_iff.mp hB
  fin_cases a <;> fin_cases b
  · exact (hzero B hweight hnontrivial).elim
  · exact hend B hweight
  · exact hmiddle B 0 hweight
  · exact hmiddle B 1 hweight

/-- Every nontrivial exceptional basic rational irreducible F4 factor over
the algebraic closure of a finite field of characteristic two has dimension
at least 26. All highest-weight cases are discharged by the actual action. -/
theorem basicFactorMinimum_algebraicClosure
    (E : Type u) [Field E] [Finite E] [CharP E 2] :
    BasicFactorMinimum (AlgebraicClosure E) 26 :=
  basicFactorMinimum_of_highestWeight_bounds
    zero_basicHighestWeight_not_isNontrivial
    middle_basicHighestWeight_finrank_ge
    end_basicHighestWeight_finrank_ge

end ReeF4.BinaryDegree.ExceptionalTensor
