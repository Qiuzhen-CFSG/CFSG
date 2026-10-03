module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Conjugation transitivity outside a central subgroup of index two

Suppose Z≤I≤Q≤P, the group P normalizes Q, I and Z, and Z centralizes Q.
If Z has index two in I, is exactly the Q-fixed subgroup of I, and has no
proper nontrivial P-invariant subgroup, then Q is transitive by conjugation
on I\Z. The result is stated for the literal ambient subgroups and elements;
no action instance or quotient replacement is introduced.

The common normalizer acts trivially on I/Z, so [I,Q] lies in Z. It is
P-invariant and nontrivial by the exact fixed-subgroup hypothesis; hence it
equals Z. For x outside Z, the map q↦[q,x] is a homomorphism because its
values lie in the central subgroup Z. Every point of I is in Z or xZ,
so this homomorphism's range contains [I,Q]=Z. A preimage of yx⁻¹ then
conjugates x to y.

This general translation argument supplies the elementary-eight/central-four
case in Stellmacher (9.9), Journal of Algebra 190 (1997). That application
obtains index two from the subgroup orders; no elementary-abelian or specific
order assumption is needed for the abstract result.
-/

namespace Subgroup
open scoped commutatorElement

public theorem conjugation_transitive_complement_of_central_index_two
    {G : Type*} [Group G] [Finite G]
    (P Q I Z : Subgroup G)
    (hQP : Q ≤ P) (hIQ : I ≤ Q) (hZI : Z ≤ I)
    (hindex : Z.relIndex I = 2)
    (hPQ : P ≤ normalizer (Q : Set G))
    (hPI : P ≤ normalizer (I : Set G))
    (hPZ : P ≤ normalizer (Z : Set G))
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hfixed : I ⊓ centralizer (Q : Set G) = Z)
    (hirred : ∀ J : Subgroup G, J ≤ Z → P ≤ normalizer (J : Set G) → J = ⊥ ∨ J = Z) :
    ∀ x y : G, x ∈ I → x ∉ Z → y ∈ I → y ∉ Z →
      ∃ q : G, q ∈ Q ∧ q*x*q⁻¹ = y := by
  have hcommZ : ⁅I,Q⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro q hq i hi
    have hconj : q*i*q⁻¹ ∈ I := (mem_normalizer_iff.mp (hPI (hQP hq)) i).mp hi
    have hmem : q*i*q⁻¹ ∈ Z ↔ i⁻¹ ∈ Z :=
      ((mem_normalizer_iff.mp (hPZ (hQP hq)) i).symm).trans Z.inv_mem_iff.symm
    exact (Z.subgroupOf I).mul_mem_iff_of_index_two hindex
      (a := ⟨q*i*q⁻¹,hconj⟩) (b := ⟨i⁻¹,I.inv_mem hi⟩) |>.mpr hmem
  have hnorm : P ≤ normalizer ((⁅I,Q⁆ : Subgroup G) : Set G) := by
    intro p hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hPI hp),
      mem_normalizer_iff_map_conj_eq.mp (hPQ hp)]
  have hcomm : ⁅I,Q⁆ = Z := by
    rcases hirred ⁅I,Q⁆ hcommZ hnorm with hbot | heq
    · have hIC := commutator_eq_bot_iff_le_centralizer.mp hbot
      have hIZ : I ≤ Z := (le_inf le_rfl hIC).trans_eq hfixed
      have heq : I = Z := le_antisymm hIZ hZI
      rw [heq, relIndex_self] at hindex
      omega
    · exact heq
  intro x y hx hxZ hy hyZ
  have hcommX (q : G) (hq : q ∈ Q) : ⁅q,x⁆ ∈ Z := by
    rw [← hcomm, commutator_comm]
    exact commutator_mem_commutator hq hx
  let f : Q →* G := {
    toFun := fun q => ⁅(q : G),x⁆
    map_one' := by simp
    map_mul' := by
      intro q r
      change ⁅(q : G)*(r : G),x⁆ = ⁅(q : G),x⁆ * ⁅(r : G),x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hqr : (q : G) * ⁅(r : G),x⁆ = ⁅(r : G),x⁆ * q :=
        mem_centralizer_iff.mp (hcentral (hcommX r r.property)) q q.property
      have hc : ⁅(r : G),x⁆ * ⁅(q : G),x⁆ = ⁅(q : G),x⁆ * ⁅(r : G),x⁆ :=
        mem_centralizer_iff.mp (hcentral (hcommX q q.property)) _
          (hIQ (hZI (hcommX r r.property)))
      rw [hqr, mul_inv_cancel_right, hc] }
  have hZrange : Z ≤ f.range := by
    rw [← hcomm, commutator_comm]
    apply commutator_le.mpr
    intro q hq i hi
    by_cases hiZ : i ∈ Z
    · have hone : ⁅q,i⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp (hcentral hiZ) q hq)
      rw [hone]
      exact f.range.one_mem
    have hxinv : x⁻¹*i ∈ Z :=
      (Z.subgroupOf I).mul_mem_iff_of_index_two hindex
        (a := ⟨x⁻¹,I.inv_mem hx⟩) (b := ⟨i,hi⟩) |>.mpr (by
          simp only [mem_subgroupOf,inv_mem_iff,hxZ,hiZ])
    have hzero : ⁅q,x⁻¹*i⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (hcentral hxinv) q hq)
    have heq : ⁅q,i⁆ = ⁅q,x⁆ := by
      have hh := commutatorElement_mul_right_eq_mul_conj q x (x⁻¹*i)
      simpa only [mul_inv_cancel_left, hzero, mul_one, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh
    exact ⟨⟨q,hq⟩,heq.symm⟩
  have hyx : y*x⁻¹ ∈ Z :=
    (Z.subgroupOf I).mul_mem_iff_of_index_two hindex
      (a := ⟨y,hy⟩) (b := ⟨x⁻¹,I.inv_mem hx⟩) |>.mpr (by
        simp only [mem_subgroupOf,inv_mem_iff,hxZ,hyZ])
  obtain ⟨q,hq⟩ := hZrange hyx
  refine ⟨q,q.property,?_⟩
  have hh := congrArg (fun g : G => g*x) hq
  simpa [f,commutatorElement_def,mul_assoc] using hh

end Subgroup
