module
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Mathlib.Tactic

/-!
# Elementary quotients from central binary commutators

If the commutators of A with U lie in an elementary abelian two-subgroup Z
centralized by A, every square in A centralizes U. If U is self-centralizing
in A, the literal quotient A/U therefore has exponent dividing two and is
elementary abelian. The argument uses the commutator product identity and
does not require A to be abelian or a finite group.

These elementary commutator consequences are used in the small-order branch
of Aschbacher--Smith 14.2.21, with U the elementary closure from 14.2.6.
-/

public section
namespace Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G]

/-- Central binary commutators force squares into the action kernel. -/
theorem sq_mem_centralizer_of_central_commutators
    (A U Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hAZ : A ≤ centralizer (Z : Set G)) (hcomm : ⁅A,U⁆ ≤ Z)
    {a : G} (ha : a ∈ A) : a ^ 2 ∈ centralizer (U : Set G) := by
  apply mem_centralizer_iff.mpr
  intro u hu
  have hc := hcomm (commutator_mem_commutator ha hu)
  have hac := (mem_centralizer_iff.mp (hAZ ha) _ hc).symm
  have he : ⁅a ^ 2,u⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hac,
      mul_inv_cancel_right, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian _ hc
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- A self-centralizing subgroup with central binary commutators has an elementary quotient. -/
theorem elementary_quotient_of_central_commutators
    (A U Z : Subgroup G) [IsElementaryAbelian 2 Z]
    [(U.subgroupOf A).Normal]
    (hAZ : A ≤ centralizer (Z : Set G)) (hcomm : ⁅A,U⁆ ≤ Z)
    (hcentralizer : A ⊓ centralizer (U : Set G) ≤ U) :
    IsElementaryAbelian 2 (A ⧸ U.subgroupOf A) := by
  have hsquare : ∀ x : A ⧸ U.subgroupOf A, x ^ 2 = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    change QuotientGroup.mk' (U.subgroupOf A) (a ^ 2) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcentralizer ⟨A.pow_mem a.property 2,
      sq_mem_centralizer_of_central_commutators A U Z hAZ hcomm a.property⟩
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (hsquare a)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

end Subgroup
