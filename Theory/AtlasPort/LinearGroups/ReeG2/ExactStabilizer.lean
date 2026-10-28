module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/ExactStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.DiagonalTorus
public import Theory.AtlasPort.LinearGroups.ReeG2.BorelPointAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The full stabilizer in the actual generated matrix group is the constructed Borel. -/
theorem fixes_infinity_iff_mem_borel (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (g : Ambient F)
    (hg : g ∈ generated F m) :
    pointRight g infinityPoint = infinityPoint ↔ g ∈ borel m hcard := by
  constructor
  · intro hfix
    have hp := generated_preserves_pointSet m hcard hg
      (show affinePoint m 0 0 0 ∈ pointSet m from ⟨some (0,0,0),rfl⟩)
    obtain ⟨op,hop⟩ := hp
    cases op with
    | none =>
      exfalso
      apply infinity_ne_affine m (0:F) 0 0
      exact pointRight_injective g (hfix.trans hop)
    | some p =>
      rcases p with ⟨a,b,c⟩
      change affinePoint m a b c = pointRight g (affinePoint m 0 0 0) at hop
      let u := rootElement m a b c
      have hu : u ∈ rootSubgroup m hcard := ⟨(a,b,c),rfl⟩
      have hug := rootSubgroup_le_generated m hcard hu
      have htg : g*u⁻¹ ∈ generated F m :=
        (generated F m).mul_mem hg ((generated F m).inv_mem hug)
      have hti : pointRight (g*u⁻¹) infinityPoint = infinityPoint := by
        rw [pointRight_mul]
        change pointRight u⁻¹ (pointRight g infinityPoint) = _
        rw [hfix]
        have hh := pointRight_inv_cancel u infinityPoint
        rw [pointRight_infinity_root m a b c] at hh
        exact hh
      have htz : pointRight (g*u⁻¹) (affinePoint m 0 0 0) = affinePoint m 0 0 0 := by
        rw [pointRight_mul]
        change pointRight u⁻¹ (pointRight g (affinePoint m 0 0 0)) = _
        rw [← hop,← pointRight_zero_root m hcard a b c]
        exact pointRight_inv_cancel u (affinePoint m 0 0 0)
      have ht := diagonal_generated_mem_torus m hcard _ htg
        (two_point_stabilizer_diagonal m hcard _ htg hti htz)
      have htb : g*u⁻¹ ∈ borel m hcard := (show splitTorus m ≤ borel m hcard from le_sup_right) ht
      have hub : u ∈ borel m hcard := (show rootSubgroup m hcard ≤ borel m hcard from le_sup_left) hu
      simpa using (borel m hcard).mul_mem htb hub
  · intro hb
    exact borel_fixes_infinity m hcard ⟨g,hb⟩

end Atlas.ReeG2
