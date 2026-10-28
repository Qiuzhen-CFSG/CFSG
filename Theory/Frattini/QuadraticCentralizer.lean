module

public import Theory.Frattini.BinarySquares
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# Frattini control by an elementary commutator layer

Suppose a finite two-subgroup A centralizes an elementary two-subgroup Z
and [A,V] lies in Z. The commutator formula shows that every square in A
centralizes V. Since squares generate the Frattini subgroup, Φ(A) centralizes
V as well. The second isomorphism theorem then makes AB/B elementary whenever
Φ(A) lies in B and A normalizes B.

This supplies the kernel-sensitive step in Delgado--Goldschmidt--Stellmacher,
*Groups and Graphs* (1985), proof of (11.8), printed p.176. V itself need not
be elementary abelian: only the commutator layer Z has that hypothesis.
-/

open Subgroup
open scoped commutatorElement

namespace Subgroup

/-- The Frattini subgroup of a finite two-actor centralizes a group on which
its commutators lie in a fixed elementary layer. -/
public theorem frattini_image_le_centralizer_of_elementary_commutator
    {G : Type*} [Group G] (A V Z : Subgroup G) [Finite A]
    [IsElementaryAbelian 2 Z] (hA : IsPGroup 2 A)
    (hcomm : ⁅A, V⁆ ≤ Z) (hcentral : A ≤ centralizer (Z : Set G)) :
    (frattini A).map A.subtype ≤ centralizer (V : Set G) := by
  rw [map_le_iff_le_comap, hA.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro x ⟨a, rfl⟩
  change (a : G) ^ 2 ∈ centralizer (V : Set G)
  rw [mem_centralizer_iff]
  intro v hv
  have hc : ⁅(a : G), v⁆ ∈ Z :=
    hcomm (commutator_mem_commutator a.property hv)
  have hfix : (a : G) * ⁅(a : G), v⁆ * (a : G)⁻¹ = ⁅(a : G), v⁆ := by
    have hh := mem_centralizer_iff.mp (hcentral a.property) _ hc
    rw [← hh]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hpow : ⁅(a : G), v⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc
  have hh : ⁅(a : G) ^ 2, v⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, hpow]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

/-- The actual product quotient AB/B is elementary when A normalizes B and
its Frattini image lies in B. Only relative normality is needed. -/
public theorem elementary_sup_quotient_of_frattini_image_le
    {G : Type*} [Group G] (A B : Subgroup G) [Finite A]
    (hA : IsPGroup 2 A) (hn : A ≤ normalizer (B : Set G))
    (hphi : (frattini A).map A.subtype ≤ B) :
    letI := normal_subgroupOf_sup_of_le_normalizer hn
    IsElementaryAbelian 2 ((A ⊔ B : Subgroup G) ⧸ B.subgroupOf (A ⊔ B)) := by
  let : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hn
  let : (B.subgroupOf (A ⊔ B)).Normal := normal_subgroupOf_sup_of_le_normalizer hn
  let : IsElementaryAbelian 2 (A ⧸ B.subgroupOf A) :=
    elementary_quotient_of_frattini_le hA _ (map_le_iff_le_comap.mp hphi)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hn
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

end Subgroup
