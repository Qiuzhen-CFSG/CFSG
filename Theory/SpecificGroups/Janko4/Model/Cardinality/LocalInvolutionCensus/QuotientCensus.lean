module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.FiniteData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.CentralizerBounds
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowCard
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowFusion
import Mathlib.Tactic.FinCases

/-!
# The max2 quotient involution census

The identity class has one element. Orbit--stabilizer turns lower bounds
640, 2688, and 2304 for the three actual quotient centralizers into the
requested class bounds. A subgroup of order 256 is Sylow under the permitted
local upper bound, since |Q| = 2661120 = 256 * 10395. Sylow conjugacy transfers
a checked square-one census in its finite table to every square-one element
of Q. All conjugators in these reductions are elements of Q itself.

`quotient_involution_coverage` covers every square-one element by the four
published images, including the identity. `quotient_class_bounds` proves the
bounds 1, 4158, 990, and 1155. Both require only the local upper bound on |H|;
the finite centralizer, subgroup-cardinality, table-coverage, and table-fusion
premises of the assembly reductions are discharged by the imported certificates.
The fixed matrix words and discovery witnesses are in `QuotientCensus/source/`,
with their checked arithmetic in `Program` and their exact lift identities in
`Marks`.

Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65,
A.6.1--4; matrix provenance: `TwoCoreCentralizer/source/`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus

theorem quotient_identity_class_card : Nat.card (quotientClass (q (lift 0))) = 1 := by
  rw [← marked_eq]
  change Nat.card (quotientClass 1) = 1
  have he : quotientClass 1 = ({1} : Set Q) := by
    ext v
    simp [quotientClass]
  rw [he]
  exact Nat.card_unique

def centralizerBound : Fin 4 → ℕ := ![2661120, 640, 2688, 2304]

theorem class_bound_of_centralizer (hH : Nat.card H ≤ 21799895040) (j : Fin 4)
    (hc : centralizerBound j ≤ Nat.card (Subgroup.centralizer {q (lift j)})) :
    Nat.card (quotientClass (q (lift j))) ≤ quotientBound j := by
  have hp : Nat.card (quotientClass (q (lift j))) *
      Nat.card (Subgroup.centralizer {q (lift j)}) = 2661120 := by
    exact (ConjClasses.nat_card_carrier_mul_card_centralizer (q (lift j))).trans
      (Coordinates.quotientSubgroup_card hH)
  have hle := (Nat.mul_le_mul_left (Nat.card (quotientClass (q (lift j)))) hc).trans hp.le
  have hn : 0 < centralizerBound j := by fin_cases j <;> decide
  have he : quotientBound j * centralizerBound j = 2661120 := by fin_cases j <;> decide
  rw [← he] at hle
  exact Nat.le_of_mul_le_mul_right hle hn

theorem coverage_of_sylow_table (hH : Nat.card H ≤ 21799895040)
    (S : Subgroup Q) (hcard : Nat.card S = 256)
    (hlocal : ∀ v : Q, v ∈ S → v^2 = 1 → ∃ j : Fin 4, IsConj (q (lift j)) v) :
    ∀ v : Q, v^2 = 1 → ∃ j : Fin 4, IsConj (q (lift j)) v := by
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 8) hcard
  have hind : ¬ 2 ∣ S.index := by
    have he := S.card_mul_index
    rw [hcard, Coordinates.quotientSubgroup_card hH] at he
    have hi : S.index = 10395 := by omega
    rw [hi]
    decide
  let P : Sylow 2 Q := hp.toSylow hind
  intro v hv
  by_cases he : v = 1
  · refine ⟨0, ?_⟩
    rw [← marked_eq, he]
    exact IsConj.refl 1
  · have ho : orderOf v = 2 := orderOf_eq_prime hv he
    obtain ⟨u, hu⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ho)
    have hs : u.val ∈ S := u.property
    have hu2 : u.val^2 = 1 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hu
      rw [← hg, conj_pow, hv, mul_one, mul_inv_cancel]
    obtain ⟨j, hj⟩ := hlocal u.val hs hu2
    exact ⟨j, hj.trans hu.symm⟩

/-- The three nonidentity centralizer lower bounds suffice for all four
requested class bounds, including the identity. -/
theorem quotient_bounds_of_centralizer_certificates
    (hH : Nat.card H ≤ 21799895040)
    (h1 : 640 ≤ Nat.card (Subgroup.centralizer {q (lift 1)}))
    (h2 : 2688 ≤ Nat.card (Subgroup.centralizer {q (lift 2)}))
    (h3 : 2304 ≤ Nat.card (Subgroup.centralizer {q (lift 3)})) :
    ∀ j : Fin 4, Nat.card (quotientClass (q (lift j))) ≤ quotientBound j := by
  intro j
  fin_cases j
  · exact quotient_identity_class_card.le
  · exact class_bound_of_centralizer hH 1 h1
  · exact class_bound_of_centralizer hH 2 h2
  · exact class_bound_of_centralizer hH 3 h3

/-- Finite table coverage and fusion are independent of the Sylow calculation;
this is their final transfer to the actual quotient. -/
theorem quotient_coverage_of_finite_certificates
    (hH : Nat.card H ≤ 21799895040)
    (hcard : Nat.card SylowTable.candidate = 256)
    (hcover : ∀ v ∈ SylowTable.candidate, ∃ i, v = SylowTable.table i)
    (hfusion : ∀ i : Fin 256, (SylowTable.table i)^2 = 1 →
      ∃ j : Fin 4, IsConj (q (lift j)) (SylowTable.table i)) :
    ∀ v : Q, v^2 = 1 → ∃ j : Fin 4, IsConj (q (lift j)) v := by
  apply coverage_of_sylow_table hH SylowTable.candidate hcard
  intro v hv hv2
  obtain ⟨i, rfl⟩ := hcover v hv
  exact hfusion i hv2

/-- Every square-one element of the actual quotient is conjugate inside Q
to one of the four fixed images, including the identity. -/
theorem quotient_involution_coverage (hH : Nat.card H ≤ 21799895040) :
    ∀ v : Q, v^2 = 1 → ∃ j : Fin 4, IsConj (q (lift j)) v :=
  quotient_coverage_of_finite_certificates hH SylowTable.candidate_card
    SylowTable.candidate_covered SylowTable.table_involution_coverage

/-- The four actual quotient conjugacy classes have the prescribed upper
bounds 1, 4158, 990, and 1155, using only the local order upper bound. -/
theorem quotient_class_bounds (hH : Nat.card H ≤ 21799895040) :
    ∀ j : Fin 4, Nat.card (quotientClass (q (lift j))) ≤ quotientBound j :=
  quotient_bounds_of_centralizer_certificates hH centralizer640_card_ge
    centralizer2688_card_ge centralizer2304_card_ge

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
