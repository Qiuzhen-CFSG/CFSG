module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Structure
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData

import Mathlib.Tactic.FinCases

/-!
# The actual graph centralizer of Held's max5 core

The subgroup is the intersection of the full graph-preserving group with
the centralizer of the faithfully embedded word-defined core. The seven
actors are inverses of its certified generators, matching the retained
GAP discovery convention. Membership therefore forces commutation with
every actor. The distinguished permutation is the actual fourth power
of the first max5 generator, not an abstract involution.

Source: GLS3 Table 5.3p, the extraspecial core of the 2B centralizer;
ATLAS HeG1-max5W1 and HeG1-p2058B0.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer
open Held.NormalizerGraph

@[expose] public def graphCentralizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ Subgroup.centralizer ((core 2).map (embedding 2) : Set (Equiv.Perm (Fin 2058)))

@[expose] public def actor : Fin 7 → Equiv.Perm (Fin 2058)
  | 0 => Tables2.p2⁻¹
  | 1 => Tables2.p3⁻¹
  | 2 => Tables2.p4⁻¹
  | 3 => Tables2.p5⁻¹
  | 4 => Tables2.p6⁻¹
  | 5 => Tables2.p7⁻¹
  | 6 => Tables2.p8⁻¹

public theorem actor_eq (j : Fin 7) : actor j = (embedding 2 (coreGenerator 2 j))⁻¹ := by
  fin_cases j <;> simp only [actor, Tables2.p2_eq, Tables2.p3_eq, Tables2.p4_eq,
    Tables2.p5_eq, Tables2.p6_eq, Tables2.p7_eq, Tables2.p8_eq] <;> rfl

public theorem actor_commutes (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (j : Fin 7) (x : Fin 2058) : σ (actor j x) = actor j (σ x) := by
  have hc := hσ.2 (actor j) (by
    rw [actor_eq, ← map_inv]
    exact Subgroup.mem_map.mpr ⟨_, (core 2).inv_mem (coreGenerator_mem 2 j), rfl⟩)
  exact (congrArg (fun p : Equiv.Perm (Fin 2058) => p x) hc).symm

@[expose] public def z : Equiv.Perm (Fin 2058) := Tables2.p2

public theorem z_eq : z = representation (max5First ^ 4) := by
  rw [z, Tables2.p2_eq]
  simp [embedding, coreGenerator, coreWord, localGenerator]

/-- The four remaining image pairs, to be established by finite certificates. -/
@[expose] public def PairCandidates (σ : Equiv.Perm (Fin 2058)) : Prop :=
  (σ 48 = 48 ∧ σ 0 = 0) ∨ (σ 48 = 48 ∧ σ 0 = 100) ∨
  (σ 48 = 334 ∧ σ 0 = 990) ∨ (σ 48 = 334 ∧ σ 0 = 1432)

end Held.TwoLocalCandidates.Cores.Max5Centralizer
