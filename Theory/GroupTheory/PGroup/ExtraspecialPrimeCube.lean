module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PGroup.PrimeCubeCenter
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Nonabelian groups of prime-cube order are extraspecial

The center has order p. Its quotient has order p² and cannot be cyclic,
since a cyclic central quotient forces commutativity. It is therefore
elementary abelian, giving all clauses of extraspeciality. No exponent-p
hypothesis is imposed on the original group.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
G.7.2(4),(6), printed pp.347--348. The concrete odd local subgroups of J₄,
HS and He already have certified noncommutativity and prime-cube order.
-/

open Subgroup

/-- Every nonabelian group of order p³ is extraspecial. -/
public theorem IsExtraspecial.of_noncommutative_card_prime_cube
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hc : Nat.card P = p ^ 3) (hn : ¬ IsMulCommutative P) : IsExtraspecial p P := by
  have hp : p.Prime := Fact.out
  have hz : Nat.card (center P) = p :=
    card_center_eq_prime_of_card_eq_prime_cube hc hn
  have hq : Nat.card (P ⧸ center P) = p ^ 2 := by
    have h := (center P).card_mul_index
    rw [hz, hc, index_eq_card, show p ^ 3 = p * p ^ 2 by rw [pow_succ']] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hnc : ¬ IsCyclic (P ⧸ center P) := by
    intro h
    let := h
    exact hn (isMulCommutative_of_isCyclic_quotient_center_self P)
  exact {
    center_order_p := hz
    quotient_elementary_abelian := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
      exponent_dvd_p := by rw [(not_isCyclic_iff_exponent_eq_prime hp hq).mp hnc] }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hn (center_eq_top_iff.mp h)) }
