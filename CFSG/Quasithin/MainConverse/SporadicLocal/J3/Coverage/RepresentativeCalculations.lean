module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.Elementary
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.LocalActions
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.LocalReduction

/-!
# Finite calculations for the fixed J₃ elementary representatives

The checked local actions are transitive on the nonidentity elements of E and
the order-four representative U. Matching an ambient normalizer element on the
standard involution leaves an element of its centralizer; the checked local
intersections then give N(E) ≤ localFamily 1 and N(U) ≤ localFamily 2.

The checked centralizer intersection gives C(B) = E. The fixed affine word
[5,5,5,6,5,5] normalizes E and carries B into the rank-three representative D,
so C(D) = E as well. All finite-calculation premises of `LocalReduction` are
discharged here. Only the permitted Sylow order and the explicit ambient
bound C(a) ≤ localFamily 0 remain hypotheses; the parent owns that bound.

Source: GLS, Number 3, Table 5.3h, printed p.269; the fixed degree-6156 ATLAS
J₃ model. The five representatives are a computational route to the table's
maximal-local coverage. Final coverage assembly belongs to the parent module.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

/-- The ambient normalizer of U lies in the fixed Thompson local candidate. -/
public theorem normalizer_representative_two_le
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    normalizer (elementaryRepresentative 2 : Set Model) ≤ localFamily 2 :=
  normalizer_le_local_of_transitive _ _ a_mem_elementaryRepresentative_two hC
    (localFamily_two_le_normalizer hS) (localFamily_two_transitive hS)
    (centralizer_inf_normalizer_representative_two_le hS)

/-- The ambient normalizer of E lies in the fixed affine local candidate. -/
public theorem normalizer_elementary_le
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    normalizer (elementaryCandidate : Set Model) ≤ localFamily 1 :=
  normalizer_le_local_of_transitive _ _
    (elementaryRepresentative_le_elementaryCandidate 1 a_mem_elementaryRepresentative_one) hC
    (localFamily_one_le_normalizer hS) (localFamily_one_transitive hS)
    (centralizer_inf_normalizer_elementary_le hS)

private theorem small_centralizers
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate ∧
      centralizer (elementaryRepresentative 3 : Set Model) = elementaryCandidate :=
  small_centralizers_of_finite_calculations hC (elementaryCandidate_commutative hS)
    (centralizer_inf_centralizer_representative_one_le hS hC) (rankThree_transporter hS)

/-- The ambient centralizer of the order-four representative B is exactly E. -/
public theorem centralizer_representative_one_eq
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate :=
  (small_centralizers hS hC).1

/-- The ambient centralizer of the rank-three representative D is exactly E. -/
public theorem centralizer_representative_three_eq
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    centralizer (elementaryRepresentative 3 : Set Model) = elementaryCandidate :=
  (small_centralizers hS hC).2

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
