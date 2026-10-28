/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SimpleStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Sylow

/-!
# SimpleStabilizer

Primitive actions with simple point stabilizers give simplicity criteria.
Normal transitivity reduces the argument to a regular normal subgroup or the whole group.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SimpleStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

/-! Simplicity from a simple stabilizer and a degree with distinct prime divisors. -/

namespace Atlas.GroupTheory
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

omit [FaithfulSMul G X] in
/-- In a doubly transitive action a regular normal subgroup cannot have order
with two distinct prime divisors. -/
theorem regular_normal_impossible [Finite G] [Finite X]
    [MulAction.IsMultiplyPretransitive G X 2]
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N X] (a : X)
    (hf : ∀ n : N, n • a = a → n = 1)
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    (hp : p ∣ Nat.card X) (hr : r ∣ Nat.card X) : False := by
  have hi : Function.Injective (fun n : N => n • a) := by
    intro u v huv
    change u • a = v • a at huv
    have huv' : (u⁻¹ * v) • a = a := by
      rw [mul_smul, ← huv, inv_smul_smul]
    exact inv_mul_eq_one.mp (hf _ huv')
  have hc : Nat.card N = Nat.card X :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hi, fun x => MulAction.exists_smul_eq N a x⟩)
  have hord : ∀ u v : N, u ≠ 1 → v ≠ 1 → orderOf u = orderOf v := by
    intro u v hu hv
    have hua : a ≠ u • a := fun h => hu (hf u h.symm)
    have hva : a ≠ v • a := fun h => hv (hf v h.symm)
    obtain ⟨k, hka, hku⟩ := (MulAction.is_two_pretransitive_iff.mp
      (inferInstance : MulAction.IsMultiplyPretransitive G X 2)) hua hva
    have hkia : k⁻¹ • a = a := by
      rw [inv_smul_eq_iff, hka]
    have he : MulAut.conjNormal k u = v := by
      apply hi
      change (k * (u : G) * k⁻¹) • a = v • a
      rw [mul_smul, mul_smul, hkia]
      exact hku
    have ho := (MulAut.conjNormal k).orderOf_eq u
    rw [he] at ho
    exact ho.symm
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := N) p (hc.symm ▸ hp)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := N) r (hc.symm ▸ hr)
  have hune : u ≠ 1 := by
    intro h
    exact (Fact.out : p.Prime).ne_one (hu.symm.trans (by rw [h, orderOf_one]))
  have hvne : v ≠ 1 := by
    intro h
    exact (Fact.out : r.Prime).ne_one (hv.symm.trans (by rw [h, orderOf_one]))
  exact hpr (hu.symm.trans ((hord u v hune hvne).trans hv))

/-- A faithful doubly transitive group with simple point stabilizer is simple
when the degree has two distinct prime divisors. -/
theorem simple_of_simple_stabilizer [Finite G] [Finite X]
    [h2 : MulAction.IsMultiplyPretransitive G X 2] (a : X)
    [IsSimpleGroup (MulAction.stabilizer G a)]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    (hp : p ∣ Nat.card X) (hr : r ∣ Nat.card X) : IsSimpleGroup G := by
  let K := MulAction.stabilizer G a
  have : Nontrivial G := Function.Injective.nontrivial K.subtype_injective
  have : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  constructor
  intro N hnormal
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have : MulAction.IsPretransitive N X := normal_pretransitive N hN
  rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply regular_normal_impossible N a _ p r hpr hp hr
    intro n hn
    have hmem : (⟨n.val,hn⟩ : K) ∈ N.subgroupOf K := n.property
    rw [hbot, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    exact congrArg (fun k : K => (k : G)) hmem
  · apply top_unique
    intro g _
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a (g • a)
    have hk : (n.val⁻¹ * g) ∈ K := by
      change (n.val⁻¹ * g) • a = a
      rw [mul_smul, ← hn]
      exact inv_smul_smul n.val a
    have hnk : (n.val⁻¹ * g) ∈ N := by
      have : (⟨n.val⁻¹ * g,hk⟩ : K) ∈ N.subgroupOf K := by rw [htop]; trivial
      exact this
    simpa using N.mul_mem n.property hnk

end Atlas.GroupTheory
