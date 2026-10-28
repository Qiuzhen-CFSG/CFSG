module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularLines
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.Faithful
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.Relations
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.PerpendicularOrbit
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.NonperpendicularOrbit
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.RankThree

/-!
# Faithfulness and primitivity of the Spin singular-line action

The natural Clifford Spin action on singular projective lines is faithful in
characteristic two and primitive over an algebraically closed field. Faithfulness
and the coordinate orbit calculations are re-exported from the modules below.

The two base-line stabilizer orbits are the perpendicular lines other than the
base, and the nonperpendicular lines. Their concrete matrix proofs lift elementary
orthogonal isometries through the Spin cover. Conjugation transports those orbit
statements to every point. The four explicit lines through e₀, e₁, f₀ and f₀ + f₁
then rule out nontrivial blocks. This primitivity argument works in every
characteristic.

This is the singular-line geometry used in the type-D argument behind GLS3,
Chapter 1, 1.10.1(b), with Ω the commutator of the full isometry group as in
1.10.7. No abstract simplicity or algebraic inverse to the Spin cover is used.
The adapted rank-three and perpendicularity arguments retain the ATLAS
attribution in their owning modules and LICENSES/ATLAS.txt.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open SingularGeometry
variable (k : Type*) [Field k] [IsAlgClosed k]

/-- Two concrete base-stabilizer orbit calculations suffice for primitivity. -/
theorem singularLines_preprimitive_of_base_orbits
    (hperp : ∀ p q : SingularLines k,
      p ≠ baseLine k → q ≠ baseLine k →
      SingularPerp k (baseLine k) p → SingularPerp k (baseLine k) q →
      ∃ g : MulAction.stabilizer (Points k) (baseLine k), g • p = q)
    (hnonperp : ∀ p q : SingularLines k,
      ¬ SingularPerp k (baseLine k) p → ¬ SingularPerp k (baseLine k) q →
      ∃ g : MulAction.stabilizer (Points k) (baseLine k), g • p = q) :
    MulAction.IsPreprimitive (Points k) (SingularLines k) := by
  let := singularLines_pretransitive k
  have hRelated (x y z : SingularLines k) (hy : y ≠ x) (hz : z ≠ x)
      (hxy : SingularPerp k x y) (hxz : SingularPerp k x z) :
      ∃ g : MulAction.stabilizer (Points k) x, g • y = z := by
    exact stabilizer_transport_from_base (baseLine k)
      (fun a b => b ≠ a ∧ SingularPerp k a b)
      (fun g a b => by simp only [ne_eq, smul_left_cancel_iff, singularPerp_smul_iff])
      (fun a b ha hb => hperp a b ha.1 hb.1 ha.2 hb.2)
      x y z ⟨hy, hxy⟩ ⟨hz, hxz⟩
  have hNonrelated (x y z : SingularLines k)
      (hxy : ¬ SingularPerp k x y) (hxz : ¬ SingularPerp k x z) :
      ∃ g : MulAction.stabilizer (Points k) x, g • y = z :=
    stabilizer_transport_from_base (baseLine k)
      (fun a b => ¬ SingularPerp k a b)
      (fun g a b => (singularPerp_smul_iff k g a b).not)
      hnonperp x y z hxy hxz
  apply primitive_of_two_suborbits_and_crossing
    (baseLine k) (eLine k 1) (fLine k 0) (crossingLine k)
    (SingularPerp k) (singularPerp_symmetric k) hRelated hNonrelated
    (eLine_one_ne_base k) (fLine_zero_ne_eLine_one k)
  · exact singularPerp_eLine_eLine k 0 1
  · change ¬ SingularPerp k (eLine k 0) (fLine k 0)
    rw [singularPerp_eLine_fLine_iff]
    simp
  · exact (singularPerp_eLine_fLine_iff k 1 0).mpr (by decide)
  · exact crossingLine_not_perp_base k
  · exact crossingLine_not_perp_eLine_one k

/-- The native Clifford Spin action on singular lines is primitive over an
algebraically closed field, in every characteristic. -/
theorem singularLines_preprimitive :
    MulAction.IsPreprimitive (Points k) (SingularLines k) :=
  singularLines_preprimitive_of_base_orbits k
    (singularLines_base_perpendicular_transitive k)
    (singularLines_base_nonperpendicular_transitive k)

end Triality.SimplyConnected.NormalRootExtraction
