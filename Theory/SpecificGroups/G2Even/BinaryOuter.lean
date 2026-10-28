module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.GroupTheory.NormalizerOuterPGroup

/-!
# The outer two-group of the actual binary G₂ derived group

The proved full-group conjugation theorem realizes every automorphism of
G₂(2)′. Hence G₂(2)/G₂(2)′, of order two, surjects onto its outer group.
The calculation uses the actual octonion commutator and conjugation maps.

Source: Aschbacher--Smith A.3.18 and F.1.12, printed pp.51--52 and 263--264.
The underlying binary group calculations are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
namespace Atlas.G2
open LieAutomorphismExtensions

/-- Full binary G₂ conjugation realizes every automorphism of its derived
subgroup, so its quotient of order two surjects onto the outer group. -/
theorem binaryDerived_outer_isTwoGroup :
    IsPGroup 2 (MulAut.Outer (commutator (Model (ZMod 2)))) := by
  have hc : Nat.card (Model (ZMod 2) ⧸ BinaryDerived) = 2 ^ 1 := by
    rw [← index_eq_card, binaryDerived_eq, BinaryException.index_H,pow_one]
  have hs : Function.Surjective (MulAut.outerAction BinaryDerived) := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup BinaryDerived) x
    obtain ⟨g,rfl⟩ := binaryConjugation_surjective a
    exact ⟨QuotientGroup.mk' BinaryDerived g,rfl⟩
  exact (IsPGroup.of_card hc).of_surjective (MulAut.outerAction BinaryDerived) hs
end Atlas.G2
