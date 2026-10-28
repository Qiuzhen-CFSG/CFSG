module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives000
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives010
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives020
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives030
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives040
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives050
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives060
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives070
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives080
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives090
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.PairIncidence.PrimeObstructions.Representatives100

/-!
# The complete order-6912 double-coset obstruction certificate

Each of the 110 representatives lies in a specified candidate, or generates
with the base subgroup a nonidentity element killed by 5, 7, or 11. The
imported adapters reuse the checked small-power witnesses to obstruct order
6912. This file assembles them without asserting any candidate order.
Source: Aschbacher--Smith, Proposition 1.3.4, printed p.511/PDF p.528.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
open FiniteIncidence PairIncidenceCertificates

/-- Every excluded representative has an obstruction valid at order 6912. -/
public theorem representative_alternatives6912 (j : Fin 110) :
    representative j ∈ involutionMatrixLineStabilizer ∨
    representative j ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j), x ^ 6912 ≠ 1 := by
  fin_cases j
  · exact alternatives000 0
  · exact alternatives000 1
  · exact alternatives000 2
  · exact alternatives000 3
  · exact alternatives000 4
  · exact alternatives000 5
  · exact alternatives000 6
  · exact alternatives000 7
  · exact alternatives000 8
  · exact alternatives000 9
  · exact alternatives010 0
  · exact alternatives010 1
  · exact alternatives010 2
  · exact alternatives010 3
  · exact alternatives010 4
  · exact alternatives010 5
  · exact alternatives010 6
  · exact alternatives010 7
  · exact alternatives010 8
  · exact alternatives010 9
  · exact alternatives020 0
  · exact alternatives020 1
  · exact alternatives020 2
  · exact alternatives020 3
  · exact alternatives020 4
  · exact alternatives020 5
  · exact alternatives020 6
  · exact alternatives020 7
  · exact alternatives020 8
  · exact alternatives020 9
  · exact alternatives030 0
  · exact alternatives030 1
  · exact alternatives030 2
  · exact alternatives030 3
  · exact alternatives030 4
  · exact alternatives030 5
  · exact alternatives030 6
  · exact alternatives030 7
  · exact alternatives030 8
  · exact alternatives030 9
  · exact alternatives040 0
  · exact alternatives040 1
  · exact alternatives040 2
  · exact alternatives040 3
  · exact alternatives040 4
  · exact alternatives040 5
  · exact alternatives040 6
  · exact alternatives040 7
  · exact alternatives040 8
  · exact alternatives040 9
  · exact alternatives050 0
  · exact alternatives050 1
  · exact alternatives050 2
  · exact alternatives050 3
  · exact alternatives050 4
  · exact alternatives050 5
  · exact alternatives050 6
  · exact alternatives050 7
  · exact alternatives050 8
  · exact alternatives050 9
  · exact alternatives060 0
  · exact alternatives060 1
  · exact alternatives060 2
  · exact alternatives060 3
  · exact alternatives060 4
  · exact alternatives060 5
  · exact alternatives060 6
  · exact alternatives060 7
  · exact alternatives060 8
  · exact alternatives060 9
  · exact alternatives070 0
  · exact alternatives070 1
  · exact alternatives070 2
  · exact alternatives070 3
  · exact alternatives070 4
  · exact alternatives070 5
  · exact alternatives070 6
  · exact alternatives070 7
  · exact alternatives070 8
  · exact alternatives070 9
  · exact alternatives080 0
  · exact alternatives080 1
  · exact alternatives080 2
  · exact alternatives080 3
  · exact alternatives080 4
  · exact alternatives080 5
  · exact alternatives080 6
  · exact alternatives080 7
  · exact alternatives080 8
  · exact alternatives080 9
  · exact alternatives090 0
  · exact alternatives090 1
  · exact alternatives090 2
  · exact alternatives090 3
  · exact alternatives090 4
  · exact alternatives090 5
  · exact alternatives090 6
  · exact alternatives090 7
  · exact alternatives090 8
  · exact alternatives090 9
  · exact alternatives100 0
  · exact alternatives100 1
  · exact alternatives100 2
  · exact alternatives100 3
  · exact alternatives100 4
  · exact alternatives100 5
  · exact alternatives100 6
  · exact alternatives100 7
  · exact alternatives100 8
  · exact alternatives100 9

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
