module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Commutator generation across a centralizing subgroup of index two

Let T normalize Z and let Q be an index-two subgroup of T centralizing Z.
Every subgroup A of T that is not contained in Q has the same commutator
with Z as T does. No finiteness or elementary-abelian hypothesis is needed.

Choose a in A outside Q. Every element t outside Q can be written as
a * (a⁻¹ * t), where the second factor is in Q. Since that factor
centralizes Z, [t,z] = [a,z] for every z in Z. Elements of Q contribute
trivial commutators, and subgroup commutator generation gives the equality.

This elementary index-two argument supplies the V₀ commutator containment
in the distance-two part of Stellmacher (8.2), Journal of Algebra 190 (1997),
pp.37--38; source: `refs/latex/stellmacher-n-group.tex`. The proof uses only
general subgroup index and commutator APIs, with no campaign imports.
-/

namespace Subgroup
open scoped commutatorElement

/-- A subgroup crossing a centralizing index-two subgroup gives the full commutator. -/
public theorem commutator_eq_of_centralizing_index_two
    {G : Type*} [Group G] (Z Q T A : Subgroup G)
    (hTZ : T ≤ normalizer (Z : Set G)) (hQT : Q ≤ T)
    (hQZ : Q ≤ centralizer (Z : Set G)) (hindex : Q.relIndex T = 2)
    (hAT : A ≤ T) (hAQ : ¬ A ≤ Q) :
    ⁅T, Z⁆ = ⁅A, Z⁆ := by
  have _ := hTZ
  have _ := hQT
  refine le_antisymm ?_ (commutator_mono hAT le_rfl)
  obtain ⟨a, ha, haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  apply commutator_le.mpr
  intro t ht z hz
  by_cases htQ : t ∈ Q
  · have hcomm : ⁅t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (hQZ htQ) z hz).symm
    rw [hcomm]
    exact one_mem _
  have hk : a⁻¹ * t ∈ Q := by
    have hh := (Q.subgroupOf T).mul_mem_iff_of_index_two hindex
      (a := ⟨a⁻¹, T.inv_mem (hAT ha)⟩) (b := ⟨t, ht⟩)
    exact hh.mpr (by simp only [mem_subgroupOf, inv_mem_iff, haQ, htQ])
  have hkcomm : ⁅a⁻¹ * t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_iff.mp (hQZ hk) z hz).symm
  have heq : ⁅t, z⁆ = ⁅a, z⁆ := by
    have hh := commutatorElement_mul_left_eq_conj_mul a (a⁻¹ * t) z
    simpa only [mul_inv_cancel_left, hkcomm, mul_one, mul_inv_cancel, one_mul] using hh
  rw [heq]
  exact commutator_mem_commutator ha hz

end Subgroup
