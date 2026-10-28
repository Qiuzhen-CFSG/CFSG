/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechOrbitDivisibility.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechPrimeOrder
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/LeechOrbitDivisibility.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

theorem leech_subgroup_prime_divisor_le (H : Subgroup LeechIsometryGroup)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card H) : p ≤ 23 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' p hd
  apply leech_prime_order_le g.val p hp
  simpa using hg

theorem leech_orbit_card_dvd (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) : Nat.card (MulAction.orbit H x) ∣ Nat.card H := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod] at he
  exact ⟨Nat.card (MulAction.stabilizer H x),he.symm⟩

theorem leech_orbit_prime_divisor_le (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Nat.card (MulAction.orbit H x)) : p ≤ 23 :=
  leech_subgroup_prime_divisor_le H p hp (hd.trans (leech_orbit_card_dvd H x))

theorem leech_forbidden_orbit_sizes (H : Subgroup LeechIsometryGroup)
    {X : Type*} [MulAction H X] (x : X) :
    Nat.card (MulAction.orbit H x) ≠ 98256 ∧
    Nat.card (MulAction.orbit H x) ≠ 99408 ∧
    Nat.card (MulAction.orbit H x) ≠ 926 := by
  refine ⟨?_,?_,?_⟩
  · intro he
    have h := leech_orbit_prime_divisor_le H x 89 (by norm_num) (by rw [he]; norm_num)
    omega
  · intro he
    have h := leech_orbit_prime_divisor_le H x 109 (by norm_num) (by rw [he]; norm_num)
    omega
  · intro he
    have h := leech_orbit_prime_divisor_le H x 463 (by norm_num) (by rw [he]; norm_num)
    omega

end Atlas.Conway
