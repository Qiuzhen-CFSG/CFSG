module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ExceptionalGap

/-!
# Exceptional basic F4 bounds over algebraically closed fields

The actual normalizer and root-coefficient arguments prove the basic minimum
over every algebraically closed field of characteristic two. The stronger
middle-node orbit bound reduces every nontrivial basic factor of dimension
less than 52 to the last fundamental highest weight.

The exact end-node degree still needs an upper bound. The final conditional
assembly makes its two independent inputs explicit: existence of one genuine
end-node factor of degree at most 26 and highest-weight uniqueness. Constructing
the former and supplying the latter establishes the full small-degree gap;
the lower-bound and orbit arguments alone do not establish it.

Source: GLS3, Theorem 1.14.6(c), Section 1.14, and Definition 2.8.1(b);
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.356.
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The end-node lower bound over any algebraically closed field of
characteristic two, from the actual Weyl action and short-A2 multiplicity. -/
theorem end_basicHighestWeight_finrank_ge_charTwo
    (B : AlgebraicFactor F) (h : B.HasBasicHighestWeight (0, 1)) :
    26 ≤ Module.finrank F B.Space :=
  end_basicHighestWeight_finrank_ge_of_weight_spaces B
    (EndNode.endOrbitWeight_occurs B h)
    (EndNode.Multiplicity.zero_weight_finrank_ge_two B
      (EndNode.hasShortA2HighestVector B h))

/-- Every nontrivial exceptional basic rational irreducible F4 factor has
dimension at least 26 in characteristic two. -/
theorem basicFactorMinimum_charTwo : BasicFactorMinimum F 26 :=
  basicFactorMinimum_of_highestWeight_bounds
    zero_basicHighestWeight_not_isNontrivial
    middle_basicHighestWeight_finrank_ge
    end_basicHighestWeight_finrank_ge_charTwo

omit [CharP F 2] in
/-- Neither middle-node basic weight has degree strictly between 26 and 52. -/
theorem middle_basicHighestWeight_not_between_26_52
    (B : AlgebraicFactor F) (b : Fin 2)
    (h : B.HasBasicHighestWeight (1, b)) :
    ¬ (26 < Module.finrank F B.Space ∧ Module.finrank F B.Space < 52) := by
  exact fun hgap => (not_lt_of_ge
    (ZeroAndMiddle.middle_basicHighestWeight_finrank_ge_52 B b h)) hgap.2

/-- Below degree 52 the last fundamental highest weight is the only
possible nontrivial exceptional basic weight. -/
theorem end_highestWeight_of_basic_finrank_lt_52
    (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic) (hnt : B.IsNontrivial)
    (hdim : Module.finrank F B.Space < 52) : B.HasBasicHighestWeight (0, 1) := by
  obtain ⟨⟨a, b⟩, hw⟩ := B.isExceptionalBasic_iff.mp hB
  fin_cases a <;> fin_cases b
  · exact (zero_basicHighestWeight_not_isNontrivial B hw hnt).elim
  · exact hw
  · exact (not_lt_of_ge
      (ZeroAndMiddle.middle_basicHighestWeight_finrank_ge_52 B 0 hw) hdim).elim
  · exact (not_lt_of_ge
      (ZeroAndMiddle.middle_basicHighestWeight_finrank_ge_52 B 1 hw) hdim).elim

/-- A small end-node model and actual highest-weight uniqueness give exact
degree 26 for every end-node factor. Both construction inputs are explicit. -/
theorem end_basicHighestWeight_finrank_eq_of_model
    (hmodel : ∃ C : AlgebraicFactor F, C.HasBasicHighestWeight (0, 1) ∧
      Module.finrank F C.Space ≤ 26)
    (hunique : ∀ B C : AlgebraicFactor F,
      B.HasBasicHighestWeight (0, 1) → C.HasBasicHighestWeight (0, 1) →
      AreEquivalentRepresentations B.action C.action)
    (B : AlgebraicFactor F) (hB : B.HasBasicHighestWeight (0, 1)) :
    Module.finrank F B.Space = 26 := by
  obtain ⟨C, hC, hdim⟩ := hmodel
  obtain ⟨e, _⟩ := hunique B C hB hC
  have hlo := end_basicHighestWeight_finrank_ge_charTwo B hB
  have heq := e.finrank_eq
  omega

/-- The small basic-factor catalogue, conditional only on a genuine
end-node model and highest-weight uniqueness. -/
theorem basicFactor_finrank_eq_26_of_lt_52_of_model
    (hmodel : ∃ C : AlgebraicFactor F, C.HasBasicHighestWeight (0, 1) ∧
      Module.finrank F C.Space ≤ 26)
    (hunique : ∀ B C : AlgebraicFactor F,
      B.HasBasicHighestWeight (0, 1) → C.HasBasicHighestWeight (0, 1) →
      AreEquivalentRepresentations B.action C.action)
    (B : AlgebraicFactor F) (hB : B.IsExceptionalBasic) (hnt : B.IsNontrivial)
    (hdim : Module.finrank F B.Space < 52) : Module.finrank F B.Space = 26 :=
  end_basicHighestWeight_finrank_eq_of_model hmodel hunique B
    (end_highestWeight_of_basic_finrank_lt_52 B hB hnt hdim)

end ReeF4.BinaryDegree.ExceptionalTensor
