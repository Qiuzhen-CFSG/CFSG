module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/GroupTheory/SolvableStabilizerSimplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.QuotientGroup.Basic
set_option warningAsError false

@[expose] public section

/-! The soluble-stabilizer version of the primitive-action simplicity criterion.
This generic lemma assumes no group order or particular finite-group construction. -/
namespace Atlas.GroupTheory
open MulAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- A faithful quasiprimitive perfect nontrivial group with a soluble point
stabilizer is simple. A nontrivial normal subgroup is transitive; the quotient
is therefore a soluble image of the stabilizer and is also perfect. -/
theorem simple_of_perfect_quasiprimitive_solvable_stabilizer
    [Nontrivial G] [Group.IsPerfect G] [IsQuasiPreprimitive G X]
    [FaithfulSMul G X] (x : X) [Group.IsSolvable (stabilizer G x)] : IsSimpleGroup G := by
  constructor
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  have hfix : fixedPoints N X ≠ Set.univ := by
    intro h
    apply hbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h y ⟨n, hn⟩
  letI : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal hfix
  let f : stabilizer G x →* G ⧸ N := (QuotientGroup.mk' N).comp (stabilizer G x).subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n,hn⟩ := exists_smul_eq N x (g • x)
    have hs : (n : G)⁻¹ * g ∈ stabilizer G x := by
      change ((n : G)⁻¹ * g) • x = x
      rw [mul_smul, ← hn]
      exact inv_smul_smul (n : G) x
    refine ⟨⟨(n : G)⁻¹ * g, hs⟩, ?_⟩
    change (QuotientGroup.mk' N) ((n : G)⁻¹ * g) = (QuotientGroup.mk' N) g
    have hnq : (QuotientGroup.mk' N) (n : G) = 1 := by
      exact (QuotientGroup.eq_one_iff _).mpr n.property
    simp [map_mul, map_inv, hnq]
  letI : Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_surjective hf
  have hsub : Subsingleton (G ⧸ N) := by
    rcases subsingleton_or_nontrivial (G ⧸ N) with h | h
    · exact h
    · exact False.elim (Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance)
  exact QuotientGroup.subgroup_eq_top_of_subsingleton N hsub
end Atlas.GroupTheory
