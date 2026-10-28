module

public import Theory.GroupTheory.Recognition.TransvectionFive.NormalizerTransport

/-!
# The measured Mathieu fusion alternatives and a normalizer-interface obstruction

The two unequal fusion counts are the numerical input in Aschbacher,
*Sporadic Groups*, §§40.3--40.5.  This file keeps the two orientations
explicit. The legacy `NormalizerTypeConsequences` interface below is preserved
for existing consumers, but its model fields do not express those source
conclusions: `pointLocal` and `planeLocal` model `N_H(Aᵢ)`, not `N_G(Aᵢ)`.

Indeed the marking identifies `N_H(Aᵢ)` with the specified binary model.
Finiteness then forces any ambient normalizer with that same abstract type to
equal `N_H(Aᵢ)` and fix `z`. The final obstruction applies this to the actual
21/45 fusion predicate and the fusion control asserted in source 39.6(3).
The fusion-control premise remains explicit; this file does not prove 39.6.

In 40.5(2), after orienting the two ends, the source instead asserts
`N_G(U₁)/U₁ ≅ L₄(2)`, `N_G(U₂) = H`,
`N_G(A₁)/A₁ ≅ L₃(2) × S₃`, and `N_G(A₂)/A₂ ≅ S₆/Z₃`.
The last notation denotes an extension with normal subgroup of order three
and quotient `S₆`, as proved in 40.4; it does not denote a quotient of `S₆`.
-/

@[expose] public section
namespace Theory.GroupTheory.TransvectionFive

open Subgroup

variable {G : Type*} [Group G] {z : G}
variable (F : MarkedCentralizer z)

/-- The two possible orientations of the measured `(21,45)` alternative. -/
public def MathieuFusionOrientation : Prop :=
  (F.fusion F.plane).ncard = 21 ∧ (F.fusion F.threeSpace).ncard = 45

/-- The opposite orientation of the measured `(21,45)` alternative. -/
public def MathieuFusionOppositeOrientation : Prop :=
  (F.fusion F.plane).ncard = 45 ∧ (F.fusion F.threeSpace).ncard = 21

/-- The numerical Mathieu alternative is exactly the disjunction of its two
orientations.  This is the source count, before any normalizer calculation. -/
public theorem mathieuFusion_iff_orientations :
    F.MathieuFusion ↔
      MathieuFusionOrientation F ∨ MathieuFusionOppositeOrientation F := by
  rfl

/-- Extract the measured orientation without choosing an orientation globally. -/
public theorem mathieuFusion_cases :
    F.MathieuFusion →
      MathieuFusionOrientation F ∨ MathieuFusionOppositeOrientation F := by
  intro h
  exact h

/-- Legacy normalizer interface, retained for compatibility.

The equalities are deliberately stated on the literal pulled-back subgroups.
The two model equivalences incorrectly compare full ambient normalizers to
relative normalizers inside the point centralizer. The obstruction below
shows that this record cannot be supplied together with the Mathieu counts
and source 39.6(3). It must not be used as the target for proving 40.3–40.5. -/
public structure NormalizerTypeConsequences where
  plane_normalizer : Subgroup G
  plane_normalizer_eq :
    normalizer (F.plane : Set G) = plane_normalizer
  threeSpace_normalizer : Subgroup G
  threeSpace_normalizer_eq :
    normalizer (F.threeSpace : Set G) = threeSpace_normalizer
  plane_normalizer_model :
    Nonempty (plane_normalizer ≃* BinaryLinear.TransvectionFiveLocal.pointLocal)
  threeSpace_normalizer_model :
    Nonempty (threeSpace_normalizer ≃*
      BinaryLinear.TransvectionFiveLocal.planeLocal)

/-- Legacy pairing of the count orientation with the normalizer interface.
This is not a source-faithful 40.3–40.5 certificate. -/
public structure MathieuLocalSourceData where
  orientation : MathieuFusionOrientation F ∨ MathieuFusionOppositeOrientation F
  consequences : NormalizerTypeConsequences F

public theorem MathieuLocalSourceData.mathieuFusion
    (D : MathieuLocalSourceData F) : F.MathieuFusion := by
  exact D.orientation

namespace NormalizerTypeConsequences

variable [Finite G] (D : NormalizerTypeConsequences F)

include D

/-- The legacy plane model forces its whole normalizer to fix `z`.
This follows from the actual relative-normalizer equivalence and finiteness. -/
theorem plane_normalizer_le_centralizer :
    normalizer (F.plane : Set G) ≤ centralizer ({z} : Set G) := by
  have hcard : Nat.card (normalizer (F.plane : Set G)) =
      Nat.card ↥(centralizer ({z} : Set G) ⊓ normalizer (F.plane : Set G)) :=
    (Nat.card_congr ((MulEquiv.subgroupCongr D.plane_normalizer_eq).trans
      D.plane_normalizer_model.some).toEquiv).trans
      (Nat.card_congr F.plane_relativeNormalizerEquiv.toEquiv).symm
  have heq := eq_of_le_of_card_ge inf_le_right hcard.le
  exact heq.symm.trans_le inf_le_left

/-- The same obstruction applies at the other end of the marked flag. -/
theorem threeSpace_normalizer_le_centralizer :
    normalizer (F.threeSpace : Set G) ≤ centralizer ({z} : Set G) := by
  have hcard : Nat.card (normalizer (F.threeSpace : Set G)) =
      Nat.card ↥(centralizer ({z} : Set G) ⊓ normalizer (F.threeSpace : Set G)) :=
    (Nat.card_congr ((MulEquiv.subgroupCongr D.threeSpace_normalizer_eq).trans
      D.threeSpace_normalizer_model.some).toEquiv).trans
      (Nat.card_congr F.threeSpace_relativeNormalizerEquiv.toEquiv).symm
  have heq := eq_of_le_of_card_ge inf_le_right hcard.le
  exact heq.symm.trans_le inf_le_left

/-- With source 39.6(3)'s normalizer control of fusion, the legacy plane
model permits at most one conjugate of `z` in the plane. -/
theorem plane_fusion_ncard_le_one
    (hcontrol : ∀ a ∈ F.fusion F.plane,
      ∃ n : normalizer (F.plane : Set G), (n : G) * z * (n : G)⁻¹ = a) :
    (F.fusion F.plane).ncard ≤ 1 := by
  have hsubset : F.fusion F.plane ⊆ {z} := by
    intro a ha
    obtain ⟨n, hna⟩ := hcontrol a ha
    have hn := mem_centralizer_singleton_iff.mp
      (D.plane_normalizer_le_centralizer F n.property)
    rw [← hna, hn]
    simp
  simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsubset

end NormalizerTypeConsequences

/-- The legacy normalizer record is incompatible with the Mathieu counts
once source 39.6(3) is supplied on the literal pulled-back plane.
This refutes the proposed intermediate interface, not the source theorem. -/
theorem no_normalizerTypeConsequences_of_plane_fusion_control [Finite G]
    (hfusion : F.MathieuFusion)
    (hcontrol : ∀ a ∈ F.fusion F.plane,
      ∃ n : normalizer (F.plane : Set G), (n : G) * z * (n : G)⁻¹ = a) :
    ¬ Nonempty (NormalizerTypeConsequences F) := by
  rintro ⟨D⟩
  have hle := D.plane_fusion_ncard_le_one F hcontrol
  rcases hfusion with h | h <;> rw [h.1] at hle <;> omega

end Theory.GroupTheory.TransvectionFive
