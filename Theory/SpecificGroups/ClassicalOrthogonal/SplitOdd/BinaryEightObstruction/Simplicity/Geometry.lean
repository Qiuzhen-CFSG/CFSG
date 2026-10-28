/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The block argument is the existing adaptation of
Atlas/GroupTheory/RankThreePrimitive.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, imported below.
The geometric source route is Atlas/LinearGroups/Orthogonal/SingularPrimitiveD.lean.
Changes: actual binary singular vectors, checked coordinate root traces, and
four explicit crossing points instead of arbitrary connectors.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Basic
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Geometry.Certificates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.RankThree

/-!
# Primitivity of the exact binary split-eight singular-vector action

The checked Siegel traces establish transitivity and the two nontrivial
`e₀`-stabilizer orbits: singular vectors perpendicular to `e₀` other than
`e₀`, and singular vectors not perpendicular to `e₀`. Conjugation gives the
same description at every point. The crossing points `e₀`, `e₁`, `f₀`, and
`f₀ + f₁` force a nonsingleton block to contain both suborbits, hence every
point. The abstract block criterion imports only Mathlib action theory.

All actions and group elements are those of `Simplicity.Basic`. Neither
simplicity nor perfectness nor a group order is used. The consumer is the
Iwasawa theorem `BinaryEightObstruction.isSimpleGroup_of_preprimitive` in
`Simplicity.lean`, for the Ω₈⁺(2) section of GLS3 Table 5.3l and the
Aschbacher–Smith A.2.15(2), A.2.19 application.
-/

public noncomputable section
namespace ClassicalOrthogonal.BinaryEightObstruction.Simplicity
open MulAction
open Triality.SimplyConnected.NormalRootExtraction.SingularGeometry

private def Perp (p q : Point) : Prop := Q.polarBilin p.val q.val = 0

private theorem perp_smul (g : E) (p q : Point) : Perp (g • p) (g • q) ↔ Perp p q := by
  change Q.polarBilin (linear g p.val) (linear g q.val) = 0 ↔ _
  rw [linear_polar]
  rfl

private theorem perp_symm {p q : Point} (h : Perp p q) : Perp q p := by
  change Q.polarBilin q.val p.val = 0
  rw [Quadratic.polar_swap]
  exact h

private theorem perp_base (p : Point) : Perp (pointE 0) p ↔ p.val (.inr 0) = 0 := by
  change Q.polarBilin (e 0) p.val = 0 ↔ _
  rw [Quadratic.polar_swap, polarD_e]

/-- Transitivity of the exact natural action on nonzero singular vectors. -/
theorem singular_pretransitive : IsPretransitive E Point := by
  apply (isPretransitive_iff_base (pointE 0)).mpr
  intro p
  obtain ⟨g, hg⟩ := Geometry.singular_transport p.val p.prop.1 p.prop.2
  exact ⟨g, Subtype.ext hg⟩

private theorem stabilizer_transport_of_witnesses (b y z : Point)
    (hy : ∃ g : E, g • pointE 0 = pointE 0 ∧ g • b = y)
    (hz : ∃ g : E, g • pointE 0 = pointE 0 ∧ g • b = z) :
    ∃ g : stabilizer E (pointE 0), g • y = z := by
  obtain ⟨gy, hyfix, hy⟩ := hy
  obtain ⟨gz, hzfix, hz⟩ := hz
  let sy : stabilizer E (pointE 0) := ⟨gy, hyfix⟩
  let sz : stabilizer E (pointE 0) := ⟨gz, hzfix⟩
  refine ⟨sz * sy⁻¹, ?_⟩
  have hy' : sy • b = y := hy
  have hz' : sz • b = z := hz
  rw [← hy', mul_smul, inv_smul_smul, hz']

private theorem perpendicular_base (y z : Point) (hy : y ≠ pointE 0) (hz : z ≠ pointE 0)
    (hpy : Perp (pointE 0) y) (hpz : Perp (pointE 0) z) :
    ∃ g : stabilizer E (pointE 0), g • y = z := by
  apply stabilizer_transport_of_witnesses (pointE 1)
  · obtain ⟨g, hfix, hg⟩ := Geometry.perpendicular_transport y.val y.prop.1 y.prop.2
      (fun h => hy (Subtype.ext h)) ((perp_base y).mp hpy)
    exact ⟨g, Subtype.ext hfix, Subtype.ext hg⟩
  · obtain ⟨g, hfix, hg⟩ := Geometry.perpendicular_transport z.val z.prop.1 z.prop.2
      (fun h => hz (Subtype.ext h)) ((perp_base z).mp hpz)
    exact ⟨g, Subtype.ext hfix, Subtype.ext hg⟩

private theorem nonperpendicular_base (y z : Point)
    (hpy : ¬ Perp (pointE 0) y) (hpz : ¬ Perp (pointE 0) z) :
    ∃ g : stabilizer E (pointE 0), g • y = z := by
  apply stabilizer_transport_of_witnesses (pointF 0)
  · obtain ⟨g, hfix, hg⟩ := Geometry.nonperpendicular_transport y.val y.prop.2
      (fun h => hpy ((perp_base y).mpr h))
    exact ⟨g, Subtype.ext hfix, Subtype.ext hg⟩
  · obtain ⟨g, hfix, hg⟩ := Geometry.nonperpendicular_transport z.val z.prop.2
      (fun h => hpz ((perp_base z).mpr h))
    exact ⟨g, Subtype.ext hfix, Subtype.ext hg⟩

private def crossing : Point := ⟨Geometry.decode 48, by
  constructor
  · decide +kernel
  · rw [← Geometry.fastQ_eq]
    decide +kernel⟩

/-- The exact binary split-eight singular-vector action is primitive.

The checked root traces give the two nontrivial point-stabilizer orbits.
The four coordinate crossing points then force every nonsingleton block to
contain both suborbits. -/
theorem singular_preprimitive : IsPreprimitive E Point := by
  let := singular_pretransitive
  have related (x y z : Point) (hy : y ≠ x) (hz : z ≠ x)
      (hxy : Perp x y) (hxz : Perp x z) :
      ∃ g : stabilizer E x, g • y = z := by
    apply stabilizer_transport_from_base (pointE 0) (fun p q => q ≠ p ∧ Perp p q)
      (fun g p q => by simp only [ne_eq, smul_left_cancel_iff, perp_smul])
      (fun p q hp hq => perpendicular_base p q hp.1 hq.1 hp.2 hq.2)
      x y z ⟨hy, hxy⟩ ⟨hz, hxz⟩
  have nonrelated (x y z : Point) (hxy : ¬ Perp x y) (hxz : ¬ Perp x z) :
      ∃ g : stabilizer E x, g • y = z := by
    apply stabilizer_transport_from_base (pointE 0) (fun p q => ¬ Perp p q)
      (fun g p q => by rw [perp_smul]) nonperpendicular_base x y z hxy hxz
  apply primitive_of_two_suborbits_and_crossing
    (pointE 0) (pointE 1) (pointF 0) crossing Perp
    (fun _ _ => perp_symm) related nonrelated
  · decide +kernel
  · decide +kernel
  · change Q.polarBilin (e 0) (e 1) = 0
    rw [polarD_e]
    simp [e]
  · change Q.polarBilin (e 0) (f 0) ≠ 0
    rw [polarD_f]
    simp [e]
  · change Q.polarBilin (e 1) (f 0) = 0
    rw [polarD_f]
    simp [e]
  · change Q.polarBilin (e 0) (Geometry.decode 48) ≠ 0
    rw [Quadratic.polar_swap, polarD_e]
    decide +kernel
  · change Q.polarBilin (e 1) (Geometry.decode 48) ≠ 0
    rw [Quadratic.polar_swap, polarD_e]
    decide +kernel

end ClassicalOrthogonal.BinaryEightObstruction.Simplicity
