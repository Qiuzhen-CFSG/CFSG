module

public import Theory.GroupTheory.MaximalTwoLocalElementary

/-!
# Maximal two-locals containing a fixed Sylow subgroup

A maximal two-local containing T is the normalizer of a nontrivial
**normal** elementary abelian subgroup of T. The characteristic-center
reduction first supplies an elementary subgroup A with M = N(A). Since
T normalizes A, the product TA is a two-group, so Sylow maximality puts
A inside T. No conjugation of T or of M is needed.

Consequently an intrinsic catalogue of normal elementary subgroups of T
identifies all maximal two-locals containing T by literal equality with
normalizers. This is the restricted coverage needed for condition E in
Aschbacher–Smith, printed pp.3–4, rather than characteristic-two type.
-/

namespace Theory.GroupTheory
open Subgroup

/-- An elementary normalizer witness can be chosen normal inside the supplied Sylow subgroup. -/
public theorem exists_normal_elementary_normalizer_of_sylow_le
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    ∃ R : Subgroup T, R ≠ ⊥ ∧ R.Normal ∧ IsElementaryAbelian 2 R ∧
      M = normalizer (R.map (T : Subgroup G).subtype : Set G) := by
  obtain ⟨A, hA, hEA, hMA⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hM
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) := hMA ▸ hTM
  have hAT : A ≤ (T : Subgroup G) := by
    exact sup_eq_left.mp (T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 A) hTN)
      le_sup_left)
  let R := A.subgroupOf (T : Subgroup G)
  have hmap : R.map (T : Subgroup G).subtype = A := map_subgroupOf_eq_of_le hAT
  refine ⟨R, ?_, normal_subgroupOf_of_le_normalizer hTN, ?_, ?_⟩
  · intro h
    apply hA
    rw [← hmap, h, Subgroup.map_bot]
  · let := hEA
    exact IsElementaryAbelian.subgroupOf hAT
  · rwa [hmap]

/-- An intrinsic normal elementary catalogue gives literal equality of local normalizers. -/
public theorem maximalTwoLocal_eq_of_normal_elementary_catalogue
    {G : Type*} [Group G] [Finite G] {ι : Type*} (T : Sylow 2 G)
    (A : ι → Subgroup G)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      ∃ i, R.map (T : Subgroup G).subtype = A i)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    ∃ i, M = normalizer (A i : Set G) := by
  obtain ⟨R, hR, hn, he, hM⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i, hi⟩ := hcatalogue R hR hn he
  exact ⟨i, hi ▸ hM⟩

end Theory.GroupTheory
