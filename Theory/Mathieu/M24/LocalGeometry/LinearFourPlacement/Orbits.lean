module

public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.Properties.Order
public import Mathlib.GroupTheory.Sylow

/-!
# Intransitive Sylow overgroups preserve an octad

The marked Sylow subgroup reaches all eight points of the Golay octad with
message 1817 from point 0, and all sixteen complementary points from point 1.
Short words in its four generators certify these assertions on the native
Witt-design carrier. If an overgroup moves an octad point outside the octad,
these two sets of reachable points merge, making the overgroup transitive.
Thus an intransitive overgroup preserves the octad. Sylow conjugacy transports
both the subgroup and its actual octad to any Sylow two-subgroup.

The order 1024 comes from the checked enumeration in
`SylowNormalizer.Order`; no order or model-identification premise remains.
The source-local assertion that the join is intransitive is a separate
obligation in the Chapter 1 assembly.

Source context: Aschbacher–Smith, A.3.12(14), printed pp.47–48;
GLS3, Table 5.3e, the octad-stabilizer family. The short words below were
found by a finite search and are checked by the Lean kernel.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.LinearFourPlacement

open Subgroup MulAction SylowNormalizer
open scoped Pointwise

private def octadPoints : Finset (Fin 24) := {0, 3, 4, 8, 9, 11, 19, 21}

private theorem octadPoints_mem : octadPoints ∈ m24Blocks := by
  have he : octadPoints = m24GolayWord 1817 := by decide +kernel
  rw [he]
  exact m24GolayWord_mem_blocks_of_card_eq_eight _ (by rw [← he]; decide +kernel)

private def walk : Fin 24 → List (Fin 4)
  | 0 => []
  | 1 => []
  | 2 => [3, 0, 2, 0]
  | 3 => [2, 0]
  | 4 => [1, 2]
  | 5 => [1, 0]
  | 6 => [0, 0, 0]
  | 7 => [1, 0, 0, 0]
  | 8 => [2]
  | 9 => [3, 2]
  | 10 => [1, 2, 0]
  | 11 => [1, 2, 0]
  | 12 => [3, 0, 1, 0]
  | 13 => [0, 1, 2, 0]
  | 14 => [2, 0]
  | 15 => [0]
  | 16 => [2, 0, 1, 0]
  | 17 => [3, 2, 0]
  | 18 => [0, 1, 0]
  | 19 => [0]
  | 20 => [0, 0]
  | 21 => [0, 2]
  | 22 => [0, 2, 0]
  | _ => [2, 0, 0, 0]

private theorem walk_check (x : Fin 24) :
    evaluatePoint (walk x) (if x ∈ octadPoints then 0 else 1) = x := by
  fin_cases x <;> decide +kernel

private theorem reach_inside (x : Fin 24) (hx : x ∈ octadPoints) :
    ∃ c : candidate, (c : M24) • (0 : Fin 24) = x := by
  refine ⟨⟨OrderEnumeration.evaluate (walk x), OrderEnumeration.evaluate_mem _⟩, ?_⟩
  change (OrderEnumeration.evaluate (walk x)).val _ = x
  rw [OrderEnumeration.evaluate_apply]
  simpa only [if_pos hx] using walk_check x

private theorem reach_outside (x : Fin 24) (hx : x ∉ octadPoints) :
    ∃ c : candidate, (c : M24) • (1 : Fin 24) = x := by
  refine ⟨⟨OrderEnumeration.evaluate (walk x), OrderEnumeration.evaluate_mem _⟩, ?_⟩
  change (OrderEnumeration.evaluate (walk x)).val _ = x
  rw [OrderEnumeration.evaluate_apply]
  simpa only [if_neg hx] using walk_check x

private theorem transitive_of_cross (H : Subgroup M24) (hC : candidate ≤ H)
    (hcross : ∃ g : H, g • (0 : Fin 24) = 1) :
    IsPretransitive H (Fin 24) := by
  obtain ⟨g, hg⟩ := hcross
  have reach (x : Fin 24) : ∃ h : H, h • (0 : Fin 24) = x := by
    by_cases hx : x ∈ octadPoints
    · obtain ⟨c, hc⟩ := reach_inside x hx
      exact ⟨⟨c, hC c.property⟩, hc⟩
    · obtain ⟨c, hc⟩ := reach_outside x hx
      exact ⟨(⟨c, hC c.property⟩ : H) * g, by rw [mul_smul, hg]; exact hc⟩
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := reach x
  obtain ⟨b, rfl⟩ := reach y
  exact ⟨b * a⁻¹, by simp [mul_smul]⟩

private theorem stabilizes_of_not_transitive (H : Subgroup M24) (hC : candidate ≤ H)
    (hnt : ¬ IsPretransitive H (Fin 24)) :
    H ≤ MulAction.stabilizer M24 octadPoints := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  by_contra houtside
  obtain ⟨a, ha⟩ := reach_inside x hx
  obtain ⟨b, hb⟩ := reach_outside (g • x) houtside
  apply hnt (transitive_of_cross H hC ?_)
  refine ⟨(⟨b, hC b.property⟩ : H)⁻¹ * ⟨g, hg⟩ * ⟨a, hC a.property⟩, ?_⟩
  change ((b : M24)⁻¹ * g * (a : M24)) • (0 : Fin 24) = 1
  rw [mul_smul, mul_smul, ha, ← hb, inv_smul_smul]

private theorem transitive_of_conjugate (H : Subgroup M24) (g : M24)
    (ht : IsPretransitive (H.map (MulAut.conj g⁻¹).toMonoidHom) (Fin 24)) :
    IsPretransitive H (Fin 24) := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := ht.exists_smul_eq (g⁻¹ • x) (g⁻¹ • y)
  obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp h.property
  refine ⟨⟨k, hk⟩, ?_⟩
  have hc := congrArg (fun z : Fin 24 => g • z) hh
  change g • ((h : M24) • (g⁻¹ • x)) = g • (g⁻¹ • y) at hc
  rw [← he] at hc
  change g • ((g⁻¹ * k * g) • (g⁻¹ • x)) = g • (g⁻¹ • y) at hc
  change k • x = y
  simpa only [mul_smul, smul_inv_smul, inv_smul_smul] using hc

/-- Every intransitive overgroup of a Sylow two-subgroup preserves an actual octad. -/
public theorem intransitive_sylow_overgroup_le_octadStabilizer
    (S : Sylow 2 M24) (H : Subgroup M24) (hSH : S.toSubgroup ≤ H)
    (hnt : ¬ IsPretransitive H (Fin 24)) :
    ∃ O : Octad, H ≤ octadStabilizer O := by
  have hp : IsPGroup 2 candidate := IsPGroup.of_card
    (show Nat.card candidate = 2 ^ 10 by rw [candidate_card]; norm_num)
  have hi : ¬ 2 ∣ candidate.index := by
    have hc := candidate.card_mul_index
    rw [candidate_card, m24_order] at hc
    have he : candidate.index = 239085 := by omega
    rw [he]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 (hp.toSylow hi) S
  have hmap : candidate.map (MulAut.conj g).toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let K := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hCK : candidate ≤ K := by
    intro c hc
    apply Subgroup.mem_map.mpr
    refine ⟨(MulAut.conj g) c, hSH ?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hc
    · simp [MulAut.conj_apply, mul_assoc]
  have hK : K ≤ MulAction.stabilizer M24 octadPoints :=
    stabilizes_of_not_transitive K hCK (fun ht => hnt (transitive_of_conjugate H g ht))
  have hO : g • octadPoints ∈ m24Blocks := by
    have hm := (mem_M24_iff g.val).mp g.property
    change g.val • octadPoints ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← hm]
    exact Set.smul_mem_smul_set octadPoints_mem
  refine ⟨⟨g • octadPoints, hO⟩, ?_⟩
  change H ≤ MulAction.stabilizer M24 (g • octadPoints)
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  intro h hh
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) h, hK ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem _ hh
  · simp [MulAut.conj_apply, mul_assoc]

end Sporadic.Mathieu.M24LocalGeometry.LinearFourPlacement
