module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.BorelRank
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.FieldDegree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport

/-!
# The larger-field Borel contradiction

The actual rank-two shadow and Borel containment select PSL₃(2ⁿ) with even
n > 1 from the larger-field list. The earlier action inputs then force
n = 2: the Borel normalizes [V,Y₊], whose nontrivial image in L/Z(L) is
centralized by the literal {2,3}-residual.

The resulting PSL₃(4) identification and the actual equivalence with
L/Z(L) transfer the concrete Borel calculation to the original L.
The center need only be a two-group: every such cover has Borel three-rank
at most one, contradicting Y₊ ≤ B and m₃(Y₊) = 2. Thus the proof handles
the possible two-cover directly, without asserting centerlessness from
O(L) = 1.

`no_larger_field_component_borel` completes the larger-field paragraph
from its branch hypotheses and earlier action facts. The initial selection
of the parabolic alternatives and the binary branch remain with the parent
proof of 15.3.35.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139, using 15.3.33(3), 15.3.40 and 15.3.41.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
variable {G : Type*} [Group G] [Finite G]

/-- The endpoint when the ambient group is the source's I. -/
theorem no_psl3_four_borel (L Yplus S B : Subgroup G) [L.Normal]
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (hrank : 2 ≤ primeRank 3 Yplus) (hodd : pPrimeCore 2 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (centralizerQuotientComponent L) 3 4) : False :=
  no_rank_two_actor_in_psl3_four_borel L Yplus S B hB hYB hrank hodd
    (hmodel.of_mulEquiv (centralizerQuotientComponentEquiv L))

/-- The same endpoint in the original ambient group, retaining the relative
component and the actual centralizer quotient of I. -/
theorem no_psl3_four_component_borel (I L M Yplus S B : Subgroup G)
    [(L.subgroupOf I).Normal]
    (h : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (hmodel : ClassicalGroup.IsPSL (componentImage I L L) 3 4) : False :=
  no_rank_two_actor_in_psl3_four_borel L Yplus S B hB hYB
    h.yplus_three_rank.ge h.oddCore
    (hmodel.of_mulEquiv (componentImageCenterEquiv I L h.component_le))

/-- The larger-field branch of the final proof of 15.3.35 is impossible.
The family, degree and Borel-rank deductions are all discharged from the
actual component setup and earlier action inputs. Relative normality and
the original centralizer quotient are retained throughout. -/
theorem no_larger_field_component_borel
    (I L M Y S V V₁ V₂ Yplus B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : ActionInputs M Y S V V₁ V₂ Yplus B)
    (hfamily : LargerFieldRankTwoModel (componentImage I L L))
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B) : False := by
  obtain ⟨n, hn, _, hmodel⟩ := larger_field_linear_even I L M Yplus S B c hfamily hB hYB
  have hn2 := field_degree_eq_two c a hB hn hmodel
  subst n
  exact no_psl3_four_component_borel I L M Yplus S B c hB hYB (by simpa using hmodel)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
