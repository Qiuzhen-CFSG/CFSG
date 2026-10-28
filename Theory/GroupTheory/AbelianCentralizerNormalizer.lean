module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normal self-centralizing p-subgroups from abelian centralizers

If A is abelian and C_G(A) is a p-group, its restriction to N_G(A) is
normal and self-centralizing there. Indeed A lies in C_G(A), so an element
centralizing C_G(A) already centralizes A. This avoids computing the entire
normalizer or identifying its quotient.

This standard centralizer argument is used for the elementary four- and
eight-subgroups of HS in the even-characteristic calculation; see
Aschbacher–Smith, condition E, printed pp.3–4, and GLS3 Table 5.3m.
-/

namespace Theory.GroupTheory
open Subgroup

/-- The intrinsic centralizer provides the required normal self-centralizing p-subgroup. -/
public theorem exists_normal_selfCentralizing_pSubgroup_of_abelian_centralizer
    {G : Type*} [Group G] {p : ℕ} (A : Subgroup G) [IsMulCommutative A]
    (hp : IsPGroup p (centralizer (A : Set G))) :
    ∃ Q : Subgroup (normalizer (A : Set G)), Q.Normal ∧ IsPGroup p Q ∧
      centralizer (Q : Set (normalizer (A : Set G))) ≤ Q := by
  let Q := (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))
  refine ⟨Q, inferInstance, hp.comap_subtype, ?_⟩
  intro x hx
  change (x : G) ∈ centralizer (A : Set G)
  intro a ha
  let aN : normalizer (A : Set G) := ⟨a, A.le_normalizer ha⟩
  have haQ : aN ∈ Q := A.le_centralizer ha
  exact congrArg Subtype.val (hx aN haQ)

end Theory.GroupTheory
