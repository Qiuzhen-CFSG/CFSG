module

public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Lines

/-!
# Displacement and faithfulness of a singular-line residual

In the rotation group, the stabilizer of each singular graph contains a
simultaneous nonidentity rotation of both definite planes. Its displacement
map is bijective on the four-space. Also, a pair of plane rotations fixing
a singular line pointwise is the identity. These finite computations are
checked by the Lean kernel, and the proved graph classification and residual
identity transport them to every totally singular four-subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66(5), printed p.1152, PDF p.1169.
-/

@[expose] public section

open Subgroup
namespace OrthogonalFourBinary.TerminalLines

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_displacement : ∀ i : LineCode, ∃ k : RotationCode,
    (∀ v : Space, (rotation k v).2 = planePermutation i (rotation k v).1 ↔
      v.2 = planePermutation i v.1) ∧
    ∀ w : Space, ∃ v : Space, rotation k v - v = w := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_faithfulness : ∀ i : LineCode, ∀ k : RotationCode,
    (∀ v : Space, v.2 = planePermutation i v.1 → rotation k v = v) → k = 1 := by
  decide +kernel

/-- One element of the line residual has a surjective displacement map on the whole space. -/
theorem lineResidual_displacement_surjective (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0) :
    ∃ g ∈ lineResidual E, Function.Surjective
      (fun v : Multiplicative Space => vectorAction g v * v⁻¹) := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  obtain ⟨k,hk,hmove⟩ := finite_displacement i
  refine ⟨rotationHom k, ?_, ?_⟩
  · rw [lineResidual_eq_rotations_inter]
    exact ⟨⟨k,rfl⟩,hk⟩
  · intro w
    obtain ⟨v,hv⟩ := hmove w.toAdd
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    change rotation k v + -v = w.toAdd
    simpa only [sub_eq_add_neg] using hv

/-- The orthogonal line residual acts faithfully on the actual singular line. -/
theorem lineResidual_faithful_on_line (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0)
    (g : IsometryGroup) (hg : g ∈ lineResidual E)
    (hfix : ∀ v : E, vectorAction g (v : Multiplicative Space) = v) : g = 1 := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  rw [lineResidual_eq_rotations_inter] at hg
  obtain ⟨k,rfl⟩ := hg.1
  have hk : k = 1 := finite_faithfulness i k (fun v hv => hfix ⟨Multiplicative.ofAdd v,hv⟩)
  rw [hk, map_one]

/-- The line residual, like the full rotation group, has exponent dividing three. -/
theorem lineResidual_cube (E : Subgroup (Multiplicative Space))
    (g : IsometryGroup) (hg : g ∈ lineResidual E) : g ^ 3 = 1 := by
  rw [lineResidual_eq_rotations_inter] at hg
  obtain ⟨i,rfl⟩ := hg.1
  exact rotation_cube i

end OrthogonalFourBinary.TerminalLines
