module

public import GorensteinWalter.Section2.Basic
public import GorensteinWalter.Section4.Defs
public import GorensteinWalter.Section4.SecondCaseComponentData
public import GorensteinWalter.Section4.SecondCaseEquationTen
public import GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import GorensteinWalter.Section4.SecondCaseEquationEleven
public import GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import GorensteinWalter.PGammaL2PSLRangeCentralizer
import GorensteinWalter.Section4.SecondCaseA7OmegaData
import GorensteinWalter.Section4.SecondCaseA7CountData
import GorensteinWalter.Section4.SecondCaseA7CountContradiction
import GorensteinWalter.Section4.SecondCaseLinearContradictionDataCore

/-!
# Section 4: elimination of the second case
-/

noncomputable section

open Matrix

namespace GorensteinWalter

universe u

/-! ## Section 4: elimination of the second case -/

/-- The `A₇` component alternative is too large: the index estimate in the
middle of Section 4 gives a contradiction. -/
public theorem secondCase_alternatingComponent_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty
      ((d.E ⧸ Subgroup.center d.E) ≃* alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    False := by
  obtain ⟨od⟩ := secondCase_a7_omegaData hmin c w d hA7 hmodel
  exact secondCase_a7_impossible_of_countData hmin c w d hA7 hmodel
    (secondCase_a7_countData hmin c w d hA7 hmodel od)

/-- Equations (10), (11), and (12), followed by the final estimate, produce
the impossible numerical data above. -/
public theorem secondCase_linearContradictionData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hKprimePower : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hmodel : d.model = ComponentQuotientModel.projectiveSpecialLinear
      K hKprimePower e) :
    LinearCaseContradictionData := by
  exact secondCase_linearContradictionData_core hmin c w d K hKprimePower e hmodel

/-- The final inequality `q(q - 4) < 7` contradicts `q ≥ 7`. -/
public theorem linearCaseContradiction
    (d : LinearCaseContradictionData) : False := by
  rcases d with ⟨q, k, k', p, p0, p1, u, hq, hk, hk', hp, hu, hineq⟩
  have hqminus : 3 ≤ q - 4 := by
    omega
  nlinarith [hineq]

/-- Section 4 eliminates case (2) of Theorem 2.10. -/
public theorem secondCase_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hsecond : SecondCase c) :
    False := by
  let w := hsecond.some
  obtain ⟨d⟩ := secondCase_componentData hmin c w
  cases hmodel : d.model with
  | alternating e =>
      exact secondCase_alternatingComponent_impossible hmin c w d e hmodel
  | projectiveSpecialLinear K hKprimePower e =>
      exact linearCaseContradiction
        (secondCase_linearContradictionData hmin c w d K hKprimePower e hmodel)

end GorensteinWalter
