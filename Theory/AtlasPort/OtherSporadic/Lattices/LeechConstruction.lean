/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechConstruction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrossGeometry
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechVisibleSymmetries
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetSigns
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetPermutations

/-!
The concrete Leech lattice with its short shells, crosses, and visible sextet symmetries.
The final construction assembles the proved lattice, counting, geometry, and equivariance results.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

/-- Job 12 on the retained Golay lattice, including explicit sextet crosses. -/
structure LeechConstruction : Prop where
  lattice : LatticeConstruction
  symmetries : VisibleSymmetryConstruction
  shells : SmallShellConstruction
  intrinsic : IntrinsicCrossConstruction
  sextet_vectors : ∀ S b, crossIntegerVectors (sextetCross S b) = sextetIntegerVectors S b
  sextet_injective : Function.Injective (fun p : UnorderedSextet × Bit => sextetCross p.1 p.2)
  sextet_count : sextetCrosses.card = 3542
  sign_parity_independent : ∀ (S : UnorderedSextet) (c : golay) (T U : {T // T ∈ S.val}),
    tetradSignParity c.val T.val = tetradSignParity c.val U.val
  permutation_action : ∀ S b g,
    crossAction (permutationIsometry g) (sextetCross S b) = sextetCross (sextetAction g S) b
  sign_action : ∀ S b c (T : {T // T ∈ S.val}),
    crossAction (signIsometry c) (sextetCross S b) =
      sextetCross S (b + tetradSignParity c.val T.val)

theorem leech_constructed : LeechConstruction where
  lattice := leech_lattice_constructed
  symmetries := leech_visible_symmetries_constructed
  shells := leech_small_shells_constructed
  intrinsic := leech_intrinsic_crosses_constructed
  sextet_vectors := sextetCross_vectors
  sextet_injective := sextetCross_injective
  sextet_count := sextetCrosses_card
  sign_parity_independent := sextetSignParity_independent
  permutation_action := sextetCross_permutation_action
  sign_action := sextetCross_sign_action

end Atlas.Lattices
