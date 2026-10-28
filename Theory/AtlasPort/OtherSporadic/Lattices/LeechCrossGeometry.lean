/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechCrossGeometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechClassTypes

/-!
The intrinsic geometry of Leech crosses.
The package assembles the class partition, cross counts, orthogonal bases, and isometry action.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

structure IntrinsicCrossConstruction : Prop where
  quadratic_space : ModTwoQuadraticConstruction
  class_counts : (shellClasses 4).card = 98280 ∧ (shellClasses 6).card = 8386560 ∧
    (shellClasses 8).card = 8292375
  classes_exhaustive : shortClasses = Finset.univ
  intrinsic_class : ∀ a, MinimumEightClass a ↔ a ∈ shellClasses 8
  crosses_count : Nat.card LeechCross = 8292375
  vectors_count : ∀ c, (crossVectors c).card = 48
  pairs_count : ∀ c : LeechCross, (normEightPairs c.val).card = 24
  orthogonal : ∀ c x y, x ∈ crossVectors c → y ∈ crossVectors c → x ≠ y → x ≠ -y →
    rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) = 0
  spans : ∀ c, Submodule.span ℚ (Set.range (crossRepresentativeVector c)) = ⊤
  transports : ∀ g c, (crossVectors c).image g.val = crossVectors (crossAction g c)
  standard : crossIntegerVectors standardCross = axisEightVectors
  type_quadratic : ∀ a, leechQuadratic a = (leechClassType a : Bit)

theorem leech_intrinsic_crosses_constructed : IntrinsicCrossConstruction where
  quadratic_space := leech_mod_two_quadratic_constructed
  class_counts := shellClasses_counts
  classes_exhaustive := shortClasses_eq_univ
  intrinsic_class := minimumEightClass_iff
  crosses_count := leechCross_card
  vectors_count := crossVectors_card
  pairs_count := crossPairs_card
  orthogonal := crossVectors_orthogonal
  spans := crossRepresentatives_span
  transports := crossVectors_transport
  standard := standardCross_vectors
  type_quadratic := leechQuadratic_classType

end Atlas.Lattices
