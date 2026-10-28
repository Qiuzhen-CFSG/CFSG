module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/GroupTheory/RankThreePrimitive.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: use four explicit crossing points in place of arbitrary connectors,
and add conjugation transport from the base stabilizer.
-/

public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# A rank-three primitivity criterion with explicit crossing points

A block contains every stabilizer orbit it meets. An edge between the two
suborbits, together with a common non-neighbor of the base and the related
representative, forces a nonsingleton block to meet both suborbits. It then
contains the entire set. Stabilizer conjugation reduces the orbit hypotheses
to a single base point. This is the geometric argument used for singular-line
actions in the type-D case of GLS3, 1.10.1(b).
-/

public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction.SingularGeometry
open MulAction
open scoped Pointwise
variable {G X : Type*} [Group G] [MulAction G X]

theorem stabilizer_transport_from_base [IsPretransitive G X]
    (a : X) (R : X → X → Prop)
    (hR : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (hbase : ∀ y z, R a y → R a z → ∃ g : stabilizer G a, g • y = z)
    (x y z : X) (hy : R x y) (hz : R x z) :
    ∃ g : stabilizer G x, g • y = z := by
  obtain ⟨g, hg⟩ := exists_smul_eq G x a
  have hy' : R a (g • y) := hg ▸ ((hR g x y).mpr hy)
  have hz' : R a (g • z) := hg ▸ ((hR g x z).mpr hz)
  obtain ⟨h, hh⟩ := hbase (g • y) (g • z) hy' hz'
  have hfix : (g⁻¹ * h.val * g) • x = x := by
    rw [mul_smul, mul_smul, hg, show h.val • a = a from h.prop,
      ← hg, inv_smul_smul]
  refine ⟨⟨g⁻¹ * h.val * g, hfix⟩, ?_⟩
  change (g⁻¹ * h.val * g) • y = z
  rw [mul_smul, mul_smul, show h.val • (g • y) = g • z from hh, inv_smul_smul]

private theorem block_contains_stabilizer_transport {B : Set X} (hB : IsBlock G B)
    {a x y : X} (ha : a ∈ B) (hx : x ∈ B)
    (hxy : ∃ g : stabilizer G a, g • x = y) : y ∈ B := by
  obtain ⟨g, hg⟩ := hxy
  have hfix : g.val • B = B := hB.stabilizer_le ha g.prop
  rw [← hg]
  change g.val • x ∈ B
  rw [← hfix, Set.smul_mem_smul_set_iff]
  exact hx

/-- A rank-three action is primitive if its two suborbits have the indicated
crossings. Four explicit points suffice; no finite counting is involved. -/
theorem primitive_of_two_suborbits_and_crossing [IsPretransitive G X]
    (a b c d : X) (R : X → X → Prop) (hSymm : ∀ ⦃x y⦄, R x y → R y x)
    (hRelated : ∀ x y z, y ≠ x → z ≠ x → R x y → R x z →
      ∃ g : stabilizer G x, g • y = z)
    (hNonrelated : ∀ x y z, ¬ R x y → ¬ R x z →
      ∃ g : stabilizer G x, g • y = z)
    (hba : b ≠ a) (hcb : c ≠ b) (hab : R a b) (hac : ¬ R a c)
    (hbc : R b c) (had : ¬ R a d) (hbd : ¬ R b d) :
    IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hs : ∀ x ∈ B, x = a
  · left
    intro x hx y hy
    exact (hs x hx).trans (hs y hy).symm
  push Not at hs
  obtain ⟨x, hx, hxa⟩ := hs
  have hboth : b ∈ B ∧ c ∈ B := by
    by_cases hax : R a x
    · have hb : b ∈ B := block_contains_stabilizer_transport hB ha hx
        (hRelated a x b hxa hba hax hab)
      exact ⟨hb, block_contains_stabilizer_transport hB hb ha
        (hRelated b a c hba.symm hcb (hSymm hab) hbc)⟩
    · have hc : c ∈ B := block_contains_stabilizer_transport hB ha hx
        (hNonrelated a x c hax hac)
      have hd : d ∈ B := block_contains_stabilizer_transport hB ha hx
        (hNonrelated a x d hax had)
      exact ⟨block_contains_stabilizer_transport hB hd ha
        (hNonrelated d a b (fun h => had (hSymm h)) (fun h => hbd (hSymm h))), hc⟩
  right
  apply Set.eq_univ_of_forall
  intro y
  by_cases hya : y = a
  · exact hya ▸ ha
  by_cases hay : R a y
  · exact block_contains_stabilizer_transport hB ha hboth.1
      (hRelated a b y hba hya hab hay)
  · exact block_contains_stabilizer_transport hB ha hboth.2
      (hNonrelated a c y hac hay)

end Triality.SimplyConnected.NormalRootExtraction.SingularGeometry
