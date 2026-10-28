module

public import Stellmacher.MainType.MathieuTwelveNonsolvable
public import Stellmacher.MainType.OmegaSixPlusTwoNonsolvable
public import Stellmacher.MainType.EightSixBNonsolvable
public import Stellmacher.MainType.EightSixCNonsolvable

/-!
# The nonsolvable two-local addendum to Theorem 1

Each of the last four source-local types supplies a nonsolvable two-local
subgroup of the ambient finite group. The Mathieu type uses its involution
centralizer; the three orthogonal types use the normalizers encoded in their
precise local configurations. The four proved type-level implications combine
directly, so no global solvability hypothesis or selected terminal pair is
needed. In particular these four types cannot occur in an N2-group.

Source: Stellmacher, Journal of Algebra 190 (1997), the final assertion of
Theorem 1 and the type definitions following (8.6), (9.1), and (10.1).
-/

namespace Stellmacher
universe u

public theorem theorem_one_nonsolvable_twoLocal
    {H : Type u} [Group H] [Finite H]
    (htype : IsOfMathieuTwelveType H ∨ IsOfOmegaSixPlusTwoType H ∨
      IsOfOmegaSixMinusThreeType H ∨ IsOfOmegaEightPlusThreeType H) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  rcases htype with hMathieu | hPlus | hMinus | hEight
  · exact exists_nonsolvable_twoLocal_of_mathieuTwelve_type hMathieu
  · exact exists_nonsolvable_twoLocal_of_omegaSixPlusTwo_type hPlus
  · exact hMinus.exists_nonsolvable_twoLocal
  · exact hEight.exists_nonsolvable_twoLocal

end Stellmacher
