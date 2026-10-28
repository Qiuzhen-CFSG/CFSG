module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Action
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation

import Mathlib.Tactic.FinCases

/-!
# Assembly reductions for Held's max5 core centralizer

The actual central involution belongs to the graph centralizer. Its checked
values interchange the second coordinates 0/100 and 990/1432 while fixing
48 and 334. Consequently four image-pair candidates, fixed-pair rigidity,
and exclusion of (334,990) suffice to leave only the identity and this
involution. Faithfulness then transports the graph bound to intrinsic
self-centralization of the max5 core.

The finite candidate, rigidity and exclusion hypotheses below are explicit
remaining obligations, not assertions of the finished source result.
Source: GLS3 Table 5.3p; the actual ATLAS max5 core and Held graph.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer
open Held.NormalizerGraph

public theorem embedding_mem (x : subgroup 2)
    (hx : x ∈ Subgroup.centralizer (core 2 : Set (subgroup 2))) :
    embedding 2 x ∈ graphCentralizer := by
  constructor
  · exact Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup x.val.property
  · rintro _ ⟨y, hy, rfl⟩
    exact (map_mul (embedding 2) y x).symm.trans
      ((congrArg (embedding 2) (hx y hy)).trans (map_mul (embedding 2) x y))

public theorem z_mem : z ∈ graphCentralizer := by
  rw [z, Tables2.p2_eq]
  apply embedding_mem
  have hh : core 2 ≤ Subgroup.centralizer ({coreGenerator 2 0} : Set (subgroup 2)) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    by_cases hj : j = 0
    · subst j; rfl
    have hpos : (0 : Fin 7).val < j.val := by
      change 0 < j.val
      exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    have he := internalConjugation 2 j 0 hpos
    have hb : commutatorBit 2 j 0 = false := by fin_cases j <;> decide
    simpa only [hb, Bool.false_eq_true, if_false, pow_zero, one_mul,
      mul_inv_eq_iff_eq_mul] using he
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hh hx)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
public theorem z_sq : z ^ 2 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem z_48 : z 48 = 48 := by decide +kernel
public theorem z_100 : z 100 = 0 := by decide +kernel
public theorem z_334 : z 334 = 334 := by decide +kernel
public theorem z_1432 : z 1432 = 990 := by decide +kernel

/-- Conditional assembly only: the two finite certificate owners discharge
candidate exhaustion, fixed-pair rigidity and the exceptional-pair obstruction. -/
public theorem eq_one_or_z_of_pair_certificates
    (hcandidates : ∀ σ ∈ graphCentralizer, PairCandidates σ)
    (hrigid : ∀ σ ∈ graphCentralizer, σ 48 = 48 → σ 0 = 0 → σ = 1)
    (hexclude : ∀ σ ∈ graphCentralizer, σ 48 = 334 → σ 0 = 990 → False)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) : σ = 1 ∨ σ = z := by
  rcases hcandidates σ hσ with h | h | h | h
  · exact Or.inl (hrigid σ hσ h.1 h.2)
  · right
    have he : z * σ = 1 := hrigid (z * σ) (graphCentralizer.mul_mem z_mem hσ)
      (by change z (σ 48) = 48; rw [h.1, z_48])
      (by change z (σ 0) = 0; rw [h.2, z_100])
    exact mul_left_cancel (he.trans (by simpa only [pow_two] using z_sq.symm))
  · exact False.elim (hexclude σ hσ h.1 h.2)
  · exact False.elim (hexclude (z * σ) (graphCentralizer.mul_mem z_mem hσ)
      (by change z (σ 48) = 334; rw [h.1, z_334])
      (by change z (σ 0) = 990; rw [h.2, z_1432]))

public theorem graphCentralizer_le_zpowers_of_pair_certificates
    (hcandidates : ∀ σ ∈ graphCentralizer, PairCandidates σ)
    (hrigid : ∀ σ ∈ graphCentralizer, σ 48 = 48 → σ 0 = 0 → σ = 1)
    (hexclude : ∀ σ ∈ graphCentralizer, σ 48 = 334 → σ 0 = 990 → False) :
    graphCentralizer ≤ Subgroup.zpowers (representation (max5First ^ 4)) := by
  intro σ hσ
  rcases eq_one_or_z_of_pair_certificates hcandidates hrigid hexclude σ hσ with rfl | rfl
  · exact (Subgroup.zpowers _).one_mem
  · rw [z_eq]
    exact Subgroup.mem_zpowers _

/-- Faithful transport of the ambient graph bound to the intrinsic local core. -/
public theorem selfCentralizing_of_graph_bound
    (hbound : graphCentralizer ≤ Subgroup.zpowers (representation (max5First ^ 4))) :
    Subgroup.centralizer (core 2 : Set (subgroup 2)) ≤ core 2 := by
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hbound (embedding_mem x hx))
  have he : coreGenerator 2 0 ^ k = x := by
    apply embedding_injective 2
    rw [map_zpow, ← Tables2.p2_eq, ← z, z_eq]
    exact hk
  rw [← he]
  exact (core 2).zpow_mem (coreGenerator_mem 2 0) k

end Held.TwoLocalCandidates.Cores.Max5Centralizer
