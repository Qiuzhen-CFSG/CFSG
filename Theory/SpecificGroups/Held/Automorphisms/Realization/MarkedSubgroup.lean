module

public import Theory.SpecificGroups.Held.Model.Transitivity
public import Mathlib.GroupTheory.Index

/-!
# The marked subgroup for Held's degree-2058 action

John Bray's ATLAS presentation specifies
`M1 = ⟨a, a^(b²), a^(b⁻²)⟩`. Here exponent conjugation means
`x^y = y⁻¹xy`, as in the source Magma file. We define this subgroup inside
the exact permutation carrier and check that its three generators have a
unique common fixed point, 1205 in zero-based numbering. Thus `M1` and its
normalizer lie in the stabilizer of that point.

Transitivity gives the point stabilizer index 2058. Consequently an upper
bound of 2058 for the index of `M1` would identify the two subgroups.

These checks do not prove that `M1` is the whole point stabilizer, or that
automorphisms preserve its conjugacy class. Those are separate obligations.
No identification with an abstract symplectic group is assumed.

Source: `Model/Source/HeG1-P1.M`, the definition of `M1`, and the literal
ATLAS tables `HeG1-p2058B0.g1` and `.g2`. The numerical fixed-point check
uses Lean kernel reduction against the existing tables.
-/

namespace Held.Realization

/-- The three involutions defining `M1` in the ATLAS presentation. -/
@[expose] public def markedGenerator : Fin 3 → He
  | 0 => a
  | 1 => (b ^ 2)⁻¹ * a * b ^ 2
  | 2 => b ^ 2 * a * (b ^ 2)⁻¹

/-- The literal subgroup `M1`, without an assumed order or identification. -/
@[expose] public def markedSubgroup : Subgroup He :=
  Subgroup.closure (Set.range markedGenerator)

/-- The common fixed point of the three marked generators, numbered from zero. -/
@[expose] public def basePoint : Fin 2058 := 1205

/-- The stabilizer in the actual Held carrier of the marked point. -/
public abbrev baseStabilizer : Subgroup He := MulAction.stabilizer He basePoint

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem markedGenerator_fixed_iff : ∀ x : Fin 2058,
    (∀ i : Fin 3, representation (markedGenerator i) x = x) ↔ x = basePoint := by
  decide +kernel

public theorem markedGenerator_mem (i : Fin 3) : markedGenerator i ∈ markedSubgroup :=
  Subgroup.subset_closure (Set.mem_range_self i)

/-- The literal subgroup has exactly one common fixed point. -/
public theorem markedSubgroup_le_stabilizer_iff (x : Fin 2058) :
    markedSubgroup ≤ MulAction.stabilizer He x ↔ x = basePoint := by
  constructor
  · intro h
    exact (markedGenerator_fixed_iff x).mp fun i => h (markedGenerator_mem i)
  · rintro rfl
    change Subgroup.closure (Set.range markedGenerator) ≤ _
    rw [Subgroup.closure_le]
    rintro g ⟨i, rfl⟩
    exact (markedGenerator_fixed_iff basePoint).mpr rfl i

public theorem markedSubgroup_le_baseStabilizer : markedSubgroup ≤ baseStabilizer :=
  (markedSubgroup_le_stabilizer_iff basePoint).mpr rfl

/-- Normalizing `M1` fixes its unique fixed point. The normalizer here is in
`He`, not in the full symmetric group. -/
public theorem markedSubgroup_normalizer_le_baseStabilizer :
    Subgroup.normalizer (markedSubgroup : Set He) ≤ baseStabilizer := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg
  have hle : markedSubgroup ≤ MulAction.stabilizer He (g • basePoint) := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hg]
    exact Subgroup.map_mono markedSubgroup_le_baseStabilizer
  exact (markedSubgroup_le_stabilizer_iff (g • basePoint)).mp hle

/-- The point stabilizer index follows from the checked transitive action. -/
public theorem baseStabilizer_index : baseStabilizer.index = 2058 := by
  rw [MulAction.index_stabilizer_of_transitive]
  simp

/-- An upper index bound suffices to identify the concrete marked subgroup
with the point stabilizer. No global group order is needed. -/
public theorem markedSubgroup_eq_baseStabilizer_of_index_le
    (hindex : markedSubgroup.index ≤ 2058) : markedSubgroup = baseStabilizer := by
  classical
  apply le_antisymm markedSubgroup_le_baseStabilizer
  by_contra h
  have hlt : markedSubgroup < baseStabilizer :=
    lt_of_le_not_ge markedSubgroup_le_baseStabilizer h
  have hi := Subgroup.index_strictAnti hlt
  rw [baseStabilizer_index] at hi
  omega

end Held.Realization
