/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalOrbitDivisibility.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumTwentyThreeCycle
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumMonomialOrbits
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeFreePermutation
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalOrbitDivisibility.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimum_point_cycle_invariant_card (a : Omega) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ orderOf g.val = 23 ∧
      ∀ S : Set (LeechShell 4),
        (∀ x, shellRepresentation 4 (permutationEmbedding g) x ∈ S ↔ x ∈ S) →
        (∀ x ∈ S, integerDot (oddProfileBase {a} ∅) x.val.val = 0) →
        23 ∣ Nat.card S := by
  obtain ⟨g,ha,ho,hf⟩ := minimum_point_cycle_no_orthogonal_fixed_vector a
  refine ⟨g,ha,ho,?_⟩
  intro S hS horth
  let f := shellRepresentation 4 (permutationEmbedding g)
  let q : Equiv.Perm S := f.subtypePerm hS
  let := Fintype.ofFinite S
  have hg : g ^ 23 = 1 := by
    apply Subtype.ext
    change g.val ^ 23 = 1
    rw [← ho,pow_orderOf_eq_one]
  have hp : f ^ 23 = 1 := by
    change (shellRepresentation 4 (permutationEmbedding g)) ^ 23 = 1
    rw [← map_pow,← map_pow,hg,map_one,map_one]
  have hq : q ^ 23 = 1 := by
    apply Equiv.ext
    intro x
    have he := congrArg (fun f : Equiv.Perm (LeechShell 4) => f x.val) hp
    apply Subtype.ext
    simpa only [q,Equiv.Perm.subtypePerm_pow,Equiv.Perm.subtypePerm_apply,Equiv.Perm.one_apply] using he
  have hfree : ∀ x : S, q x ≠ x := by
    intro x he
    have hh := congrArg (fun z : S => z.val.val.val) he
    exact hf x.val.val.val x.val.prop (horth x.val x.prop) hh
  rw [Nat.card_eq_fintype_card]
  exact Atlas.GroupTheory.prime_dvd_card_of_fixedPointFree q 23 (by decide) hq hfree

end Atlas.Conway
