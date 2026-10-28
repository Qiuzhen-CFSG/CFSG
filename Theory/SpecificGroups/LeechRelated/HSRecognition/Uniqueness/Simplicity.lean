/-
Copyright (c) 2026 Gerald Höhn.
The normal-subgroup argument is adapted from the CFSG ATLAS port of
Atlas/Conway/HSSimplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Suborbits
public import Theory.Mathieu.M22.Properties.Simplicity
public import Mathlib.GroupTheory.IsPerfect
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalOrderHundred

/-!
# Simplicity of an arbitrary rank-three extension of M₂₂

A nontrivial normal subgroup is transitive by primitivity. Its intersection
with the simple point stabilizer is either the whole stabilizer, forcing the
normal subgroup to be the whole group, or trivial, giving a regular normal
subgroup of order 100. The latter case is impossible: its characteristic
Sylow five subgroup of order 25 would also have to be transitive.

This applies the ATLAS normal-subgroup argument to the actual arbitrary
permutation group from `RankThreeData`, with the supplied Mathieu isomorphism.
No comparison with the Leech or ATLAS HS carrier is used.
-/

public section
open MulAction
namespace Sporadic.LeechRelated.HS

/-- Simplicity is a consequence of the supplied permutation geometry. -/
theorem RankThreeData.simple {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : IsSimpleGroup P := by
  classical
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card]; decide)
  let := h.primitive
  obtain ⟨e⟩ := h.stabilizer_model
  let := Sporadic.Mathieu.m22_isSimpleGroup
  let : IsSimpleGroup (stabilizer P (0 : Fin 100)) := e.isSimpleGroup
  constructor
  intro N hNnormal
  let := hNnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  let := Atlas.GroupTheory.normal_pretransitive (X := Fin 100) N hN
  let K := stabilizer P (0 : Fin 100)
  rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hbot | htop
  · have hfree (n : N) (hn : n • (0 : Fin 100) = 0) : n = 1 := by
      have hk : (⟨n.val, hn⟩ : K) ∈ N.subgroupOf K := n.property
      rw [hbot, Subgroup.mem_bot] at hk
      exact Subtype.ext (congrArg (fun k : K => (k : P)) hk)
    have hi : Function.Injective (fun n : N => n • (0 : Fin 100)) := by
      intro u v huv
      change u • (0 : Fin 100) = v • (0 : Fin 100) at huv
      have hh : (u⁻¹ * v) • (0 : Fin 100) = 0 := by
        rw [mul_smul, ← huv, inv_smul_smul]
      exact inv_mul_eq_one.mp (hfree _ hh)
    have hc : Nat.card N = 100 :=
      (Nat.card_congr (Equiv.ofBijective _ ⟨hi,
        fun x => exists_smul_eq N (0 : Fin 100) x⟩)).trans (Nat.card_fin 100)
    exact (Atlas.GroupTheory.primitive_no_normal_order_hundred (0 : Fin 100)
      (Nat.card_fin 100) N hc).elim
  · apply top_unique
    intro g _
    obtain ⟨n, hn⟩ := exists_smul_eq N (0 : Fin 100) (g • (0 : Fin 100))
    have hk : n.val⁻¹ * g ∈ K := by
      change (n.val⁻¹ * g) • (0 : Fin 100) = 0
      rw [mul_smul, ← hn]
      exact inv_smul_smul n.val (0 : Fin 100)
    have hkn : (⟨n.val⁻¹ * g, hk⟩ : K) ∈ N.subgroupOf K := by
      rw [htop]
      trivial
    have hkn' : n.val⁻¹ * g ∈ N := hkn
    have hh := N.mul_mem n.property hkn'
    simpa only [mul_inv_cancel_left] using hh
/-- Perfectness for the eventual comparison inside the full graph automorphism group. -/
theorem RankThreeData.perfect {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : Group.IsPerfect P := by
  let := h.simple
  let := h.transitive
  have hna : ¬IsMulCommutative P := by
    intro ha
    let := ha
    have he : stabilizer P (0 : Fin 100) = ⊥ := by
      apply le_antisymm _ bot_le
      intro g hg
      rw [Subgroup.mem_bot]
      apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 100)
      intro x
      obtain ⟨k, rfl⟩ := exists_smul_eq P (0 : Fin 100) x
      rw [one_smul, ← mul_smul, mul_comm' g k, mul_smul, mem_stabilizer_iff.mp hg]
    obtain ⟨e⟩ := h.stabilizer_model
    have hc := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order
    rw [he, Subgroup.card_bot] at hc
    omega
  exact ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator P) inferInstance).resolve_left
    (fun he => hna ((commutator_eq_bot_iff P).mp he))⟩

end Sporadic.LeechRelated.HS
