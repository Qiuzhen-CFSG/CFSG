module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/PointTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.GlobalPointAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem pointRight_inv_cancel (g : Ambient F) (p : Projective F) :
    pointRight g⁻¹ (pointRight g p) = p := by
  have hh := congrFun (pointRight_mul g g⁻¹) p
  simpa [pointRight_one] using hh.symm

theorem upsilon_mem_generated (m : ℕ) : (upsilon : Ambient F) ∈ generated F m :=
  Subgroup.subset_closure (Or.inr rfl)

/-- Every actual Ree point can be moved to infinity by a generated matrix. -/
theorem move_point_to_infinity (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) {p : Projective F}
    (hp : p ∈ pointSet m) :
    ∃ g : Model F m, pointRight g.val p = infinityPoint := by
  obtain ⟨op,rfl⟩ := hp
  cases op with
  | none => exact ⟨1, congrFun pointRight_one infinityPoint⟩
  | some p =>
    rcases p with ⟨a,b,c⟩
    have hu : rootElement m a b c ∈ generated F m :=
      rootSubgroup_le_generated m hcard ⟨(a,b,c),rfl⟩
    refine ⟨⟨(rootElement m a b c)⁻¹ * upsilon,
      (generated F m).mul_mem ((generated F m).inv_mem hu) (upsilon_mem_generated m)⟩,?_⟩
    change pointRight ((rootElement m a b c)⁻¹ * upsilon) (affinePoint m a b c) = _
    rw [pointRight_mul]
    change pointRight upsilon (pointRight (rootElement m a b c)⁻¹ (affinePoint m a b c)) = _
    rw [← pointRight_zero_root m hcard a b c,pointRight_inv_cancel,
      pointRight_zero_upsilon]

/-- Every ordered pair of distinct points can be moved to the two base points. -/
theorem move_pair_to_base (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) {p q : Projective F}
    (hp : p ∈ pointSet m) (hq : q ∈ pointSet m) (hpq : p ≠ q) :
    ∃ g : Model F m, pointRight g.val p = infinityPoint ∧
      pointRight g.val q = affinePoint m 0 0 0 := by
  obtain ⟨t,ht⟩ := move_point_to_infinity m hcard hp
  have hqt := generated_preserves_pointSet m hcard t.property hq
  obtain ⟨op,hop⟩ := hqt
  cases op with
  | none =>
    exfalso
    apply hpq
    exact pointRight_injective t.val (ht.trans hop)
  | some r =>
    rcases r with ⟨a,b,c⟩
    change affinePoint m a b c = pointRight t.val q at hop
    obtain ⟨u,hu,-⟩ := root_regular_on_affine m hcard a b c 0 0 0
    refine ⟨⟨t.val*u.val,(generated F m).mul_mem t.property
      (rootSubgroup_le_generated m hcard u.property)⟩,?_,?_⟩
    · change pointRight (t.val*u.val) p = _
      rw [pointRight_mul]
      change pointRight u.val (pointRight t.val p) = _
      rw [ht]
      obtain ⟨⟨d,e,f⟩,he⟩ := u.property
      rw [← he,pointRight_infinity_root]
    · change pointRight (t.val*u.val) q = _
      rw [pointRight_mul]
      change pointRight u.val (pointRight t.val q) = _
      rw [← hop]
      exact hu

/-- Double transitivity for the concrete matrix action. -/
theorem pointAction_two_pretransitive (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    letI := pointAction m hcard
    MulAction.IsMultiplyPretransitive (Model F m) (pointSet (F := F) m) 2 := by
  letI := pointAction m hcard
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨s,hs1,hs2⟩ := move_pair_to_base m hcard a.property b.property
    (fun h => hab (Subtype.ext h))
  obtain ⟨t,ht1,ht2⟩ := move_pair_to_base m hcard c.property d.property
    (fun h => hcd (Subtype.ext h))
  refine ⟨(s*t⁻¹)⁻¹,?_,?_⟩
  · apply Subtype.ext
    change pointRight (((s.val*t.val⁻¹)⁻¹)⁻¹) a.val = c.val
    rw [inv_inv,pointRight_mul]
    change pointRight t.val⁻¹ (pointRight s.val a.val) = c.val
    rw [hs1,← ht1,pointRight_inv_cancel]
  · apply Subtype.ext
    change pointRight (((s.val*t.val⁻¹)⁻¹)⁻¹) b.val = d.val
    rw [inv_inv,pointRight_mul]
    change pointRight t.val⁻¹ (pointRight s.val b.val) = d.val
    rw [hs2,← ht2,pointRight_inv_cancel]


/-- Primitivity follows from the proved double transitivity, without an order theorem. -/
theorem pointAction_preprimitive (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    letI := pointAction m hcard
    MulAction.IsPreprimitive (Model F m) (pointSet (F := F) m) := by
  letI := pointAction m hcard
  exact MulAction.isPreprimitive_of_is_two_pretransitive
    (pointAction_two_pretransitive m hcard)

end Atlas.ReeG2

