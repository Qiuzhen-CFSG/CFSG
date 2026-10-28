module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.LineOrder
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.SecondOrder

/-!
# Cubic pair incidence in the actual max2 quotient

The complete finite double-coset certificate puts any subgroup of order 6912
inside a conjugate of one of the two concrete candidates. The checked line
stabilizer order 11520 and second-candidate bound 2304 exclude both cases.

For an ambient three-core of order three, adjoining it to the pair product
would otherwise create a subgroup of order 6912. Thus the core lies in the
pair product, and its normality puts it inside the elementary-nine Sylow
three-subgroup itself. Only the three-core order remains an explicit premise;
its construction belongs to the parent max2 reducibility assembly.
Source: Aschbacher--Smith, Proposition 1.3.4, printed p.511/PDF p.528 of
refs/quasithin.pdf; GLS3 Table 5.3i.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

/-- Only the two candidate-order obstructions remain after the finite sieve. -/
public theorem order27Exclusion_of_candidate_order_obstructions
    (hline : ¬ 6912 ∣ Nat.card involutionMatrixLineStabilizer)
    (hsecond : ¬ 6912 ∣ Nat.card involutionMatrixSecondSubgroup) :
    Order27Exclusion :=
  order27Exclusion_of_certificates hline hsecond representative_alternatives6912

/-- The core is contained in the elementary factor, with the remaining finite
candidate-order calculations stated explicitly. -/
public theorem elementaryCubicContainment_of_candidate_order_obstructions
    (hC : Nat.card (pCore 3 MatrixGroup) = 3)
    (hline : ¬ 6912 ∣ Nat.card involutionMatrixLineStabilizer)
    (hsecond : ¬ 6912 ∣ Nat.card involutionMatrixSecondSubgroup) :
    ElementaryCubicContainment :=
  elementaryCubicContainment_of_order27Exclusion hC
    (order27Exclusion_of_candidate_order_obstructions hline hsecond)

/-- No subgroup of the actual matrix quotient has order 6912. -/
public theorem order27Exclusion : Order27Exclusion :=
  order27Exclusion_of_candidate_order_obstructions
    line_order_not_divisible_6912 second_order_not_divisible_6912

/-- An order-three core lies inside every elementary-nine subgroup that
permutes setwise with a Sylow two-subgroup of the actual matrix quotient. -/
public theorem elementaryCubicContainment_of_threeCore_card
    (hC : Nat.card (pCore 3 MatrixGroup) = 3) :
    ElementaryCubicContainment :=
  elementaryCubicContainment_of_order27Exclusion hC order27Exclusion

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
