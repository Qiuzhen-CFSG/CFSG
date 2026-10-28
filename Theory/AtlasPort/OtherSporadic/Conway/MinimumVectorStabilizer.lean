/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumVectorStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimalVectorOrder
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumVectorStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- The full stabilizer in the retained lattice isometry group. -/
abbrev fullVectorStabilizer (v : leech) := MulAction.stabilizer LeechIsometryGroup v

def fullVectorStabilizerTopEquiv (v : leech) :
    fullVectorStabilizer v ≃* leechVectorStabilizer ⊤ v where
  toFun g := ⟨⟨g.val,Subgroup.mem_top _⟩,g.prop⟩
  invFun g := ⟨g.val.val,g.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem full_minimum_pretransitive : MulAction.IsPretransitive LeechIsometryGroup (LeechShell 4) := by
  let := strict_overgroup_minimum_pretransitive ⊤ monomial_lt_full
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (⊤ : Subgroup LeechIsometryGroup) x y
  exact ⟨g.val,hg⟩

theorem full_shell_stabilizer_eq (r : ℤ) (x : LeechShell r) :
    MulAction.stabilizer LeechIsometryGroup x = fullVectorStabilizer x.val := by
  ext g
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

theorem minimum_vector_orbit_stabilizer (x : LeechShell 4) :
    196560 * Nat.card (fullVectorStabilizer x.val) = Nat.card LeechIsometryGroup := by
  let := full_minimum_pretransitive
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup LeechIsometryGroup x)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),
    leech_minimal_shell_card,full_shell_stabilizer_eq] at h
  exact h

theorem minimum_vector_stabilizer_order (x : LeechShell 4) :
    Nat.card (fullVectorStabilizer x.val) = 42305421312000 := by
  have h := minimum_vector_orbit_stabilizer x
  rw [leechIsometryGroup_order] at h
  omega

theorem minimum_vector_stabilizer_factorization (x : LeechShell 4) :
    Nat.card (fullVectorStabilizer x.val) = 2^18 * 3^6 * 5^3 * 7 * 11 * 23 := by
  rw [minimum_vector_stabilizer_order]
  norm_num

end Atlas.Conway
