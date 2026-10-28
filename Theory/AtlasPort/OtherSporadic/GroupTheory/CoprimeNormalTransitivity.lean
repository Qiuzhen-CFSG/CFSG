/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/CoprimeNormalTransitivity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Normal subgroups of coprime index

Normal orbits are blocks; their number divides both the index and the degree.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/CoprimeNormalTransitivity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- A normal subgroup of index coprime to the degree remains transitive. -/
theorem normal_transitive_of_coprime_index {G X : Type*} [Group G] [MulAction G X]
    [Finite G] [Finite X] [IsPretransitive G X] (N : Subgroup G) [N.Normal]
    (hc : Nat.Coprime N.index (Nat.card X)) : IsPretransitive N X := by
  constructor
  intro a b
  let B := orbit N a
  let K := stabilizer G B
  have hB : IsBlock G B := IsBlock.orbit_of_normal a
  have hNK : N ≤ K := by
    intro n hn
    change n • orbit N a = orbit N a
    exact smul_orbit (⟨n,hn⟩ : N) a
  have hi : K.index ∣ N.index := Subgroup.index_dvd_of_le hNK
  have hp := hB.ncard_block_mul_ncard_orbit_eq ⟨a,mem_orbit_self a⟩
  rw [← index_stabilizer (G := G) B] at hp
  have hj : K.index ∣ Nat.card X := ⟨B.ncard,by simpa only [mul_comm] using hp.symm⟩
  have hk : K.index = 1 := Nat.eq_one_of_dvd_coprimes hc hi hj
  have hbcard : B.ncard = Nat.card X := by
    change B.ncard * K.index = Nat.card X at hp
    simpa only [hk,mul_one] using hp
  have hu : B = Set.univ := B.eq_univ_iff_ncard.mpr hbcard
  have hb : b ∈ B := by rw [hu]; trivial
  exact mem_orbit_iff.mp hb

end Atlas.GroupTheory
