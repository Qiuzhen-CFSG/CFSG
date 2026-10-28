module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Data

/-!
# Checking the concrete Held automorphism

Kernel-checked identities show that the explicit permutation realizes the
ATLAS generator substitution and that its fifth power is an involution.
The block decomposition only bounds the cost of checking all 2058 letters.
Source: ATLAS `HeG1-a2W1`, https://brauer.maths.qmul.ac.uk/Atlas/spor/He/#auts.
-/

namespace Held.OuterInvolution

private theorem allPointsByBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 17, ∀ r : Fin 128,
      P ⟨(q.val * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) : ∀ x, P x := by
  intro x
  have hx := h ⟨x.val / 128, by omega⟩ ⟨x.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : x.val / 128 * 128 + x.val % 128 = x.val := by omega
  simpa only [he, Nat.mod_eq_of_lt x.isLt] using hx

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_0 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_1 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_2 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_3 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_4 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_5 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_6 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_7 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_8 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_9 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_10 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_11 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_12 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_13 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_14 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_15 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_a_16 : ∀ r : Fin 128,
    (implementer * atlasA * implementer⁻¹) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (atlasA) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

public theorem conj_a : implementer * atlasA * implementer⁻¹ = atlasA := by
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  exact Fin.cases conj_a_0 (Fin.cases conj_a_1 (Fin.cases conj_a_2 (Fin.cases conj_a_3 (Fin.cases conj_a_4 (Fin.cases conj_a_5 (Fin.cases conj_a_6 (Fin.cases conj_a_7 (Fin.cases conj_a_8 (Fin.cases conj_a_9 (Fin.cases conj_a_10 (Fin.cases conj_a_11 (Fin.cases conj_a_12 (Fin.cases conj_a_13 (Fin.cases conj_a_14 (Fin.cases conj_a_15 (Fin.cases conj_a_16 (fun i => Fin.elim0 i))))))))))))))))) q

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_0 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_1 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_2 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_3 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_4 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_5 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_6 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_7 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_8 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_9 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_10 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_11 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_12 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_13 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_14 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_15 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem conj_b_16 : ∀ r : Fin 128,
    (implementer * atlasB * implementer⁻¹) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = (((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

public theorem conj_b : implementer * atlasB * implementer⁻¹ = ((atlasA * atlasB ^ 2) ^ 2)⁻¹ * atlasB * (atlasA * atlasB ^ 2) ^ 2 := by
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  exact Fin.cases conj_b_0 (Fin.cases conj_b_1 (Fin.cases conj_b_2 (Fin.cases conj_b_3 (Fin.cases conj_b_4 (Fin.cases conj_b_5 (Fin.cases conj_b_6 (Fin.cases conj_b_7 (Fin.cases conj_b_8 (Fin.cases conj_b_9 (Fin.cases conj_b_10 (Fin.cases conj_b_11 (Fin.cases conj_b_12 (Fin.cases conj_b_13 (Fin.cases conj_b_14 (Fin.cases conj_b_15 (Fin.cases conj_b_16 (fun i => Fin.elim0 i))))))))))))))))) q

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_0 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_1 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_2 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_3 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_4 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_5 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_6 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_7 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_8 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_9 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_10 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_11 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_12 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_13 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_14 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_15 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tenth_power_16 : ∀ r : Fin 128,
    (implementer ^ 10) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = ((1 : Equiv.Perm (Fin 2058))) ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

public theorem tenth_power : implementer ^ 10 = (1 : Equiv.Perm (Fin 2058)) := by
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  exact Fin.cases tenth_power_0 (Fin.cases tenth_power_1 (Fin.cases tenth_power_2 (Fin.cases tenth_power_3 (Fin.cases tenth_power_4 (Fin.cases tenth_power_5 (Fin.cases tenth_power_6 (Fin.cases tenth_power_7 (Fin.cases tenth_power_8 (Fin.cases tenth_power_9 (Fin.cases tenth_power_10 (Fin.cases tenth_power_11 (Fin.cases tenth_power_12 (Fin.cases tenth_power_13 (Fin.cases tenth_power_14 (Fin.cases tenth_power_15 (Fin.cases tenth_power_16 (fun i => Fin.elim0 i))))))))))))))))) q

end Held.OuterInvolution
