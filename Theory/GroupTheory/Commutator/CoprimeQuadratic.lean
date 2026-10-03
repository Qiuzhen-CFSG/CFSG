module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Coprime quadratic subgroup actions are trivial

If R normalizes a finite solvable subgroup Q, their orders are coprime,
and [[Q,R],R]=1, then [Q,R]=1. Apply coprime commutator idempotence to
the actual conjugation action on Q. Mapping the iterated action subgroup
through Q.subtype turns its generators into ambient double commutators,
which are trivial by hypothesis. Idempotence gives the result.

This is the standard coprime-action step used in the small-quotient
contradiction of Stellmacher (9.1), journal p.46. It needs no assumption
that Q is abelian or that either subgroup is normal in the ambient group.
Source: refs/files/stellmacher-n-group.pdf, proof of (9.1)(4).
-/

open scoped commutatorElement
namespace Subgroup

public theorem commutator_eq_bot_of_coprime_quadratic
    {G : Type*} [Group G] [Finite G]
    (Q R : Subgroup G) (hnorm : R ≤ normalizer (Q : Set G))
    (hsolv : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card R) (Nat.card Q))
    (hquad : ⁅⁅Q,R⁆,R⁆ = ⊥) : ⁅Q,R⁆ = ⊥ := by
  let _ : Normalizes R Q := ⟨hnorm⟩
  have hidem := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := Q) (A := R) hsolv hcop
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator Q R hnorm
  rw [← hmap,← hidem]
  apply bot_unique
  rw [commutatorAction₂,commutatorSubgroup,MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨q,⟨r,a,ha,rfl⟩,rfl⟩
  have haM : (a : G) ∈ ⁅Q,R⁆ := by
    rw [← hmap]
    exact mem_map_of_mem Q.subtype ha
  have hmem := commutator_mem_commutator ((⁅Q,R⁆).inv_mem haM) r.property
  rw [hquad] at hmem
  change (a : G)⁻¹ * ((r : G) * (a : G) * (r : G)⁻¹) ∈ (⊥ : Subgroup G)
  simpa only [commutatorElement_def,inv_inv,
    conjMulDistribMulActionOfLeNormalizer_smul_coe,mul_assoc] using hmem
end Subgroup
