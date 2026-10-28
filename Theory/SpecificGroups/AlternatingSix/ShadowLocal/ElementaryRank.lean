module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary two-subgroups of Aut(A₆)

Every elementary abelian two-subgroup has order at most eight. Those of
order eight belong to the actual permutation-induced S₆ subgroup. In the
Sylow holomorph model, an involution outside that subgroup has at most four
commuting square-one elements. Away from its central four-group, this
number is at most eight. The marked Sylow equivalence transports these
kernel-checked finite calculations to the automorphism group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.3.12, printed pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace AlternatingSix.ShadowLocal.Holomorph
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem noncentral_bound : ∀ x : Model,
    x ^ 2 = 1 → (¬ ∃ i, centralTranspositionEmbedding i = x) →
      Fintype.card {y : Model // y ^ 2 = 1 ∧ x * y = y * x} ≤ 8 := by
  decide +kernel

private theorem outside_bound : ∀ x : Model,
    x ^ 2 = 1 → (¬ ∃ i, naturalEmbedding i = x) →
      Fintype.card {y : Model // y ^ 2 = 1 ∧ x * y = y * x} ≤ 4 := by
  decide +kernel

private theorem elementary_card_le_commuting (E : Subgroup Model)
    [IsElementaryAbelian 2 E] (x : E) :
    Nat.card E ≤ Fintype.card {y : Model // y ^ 2 = 1 ∧ (x : Model) * y = y * x} := by
  let f : E → {y : Model // y ^ 2 = 1 ∧ (x : Model) * y = y * x} :=
    fun y => ⟨y, elemPow_eq_one_of_isElementaryAbelian (y : Model) y.property,
      congrArg Subtype.val (mul_comm x y)⟩
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

theorem elementary_card_le_eight (E : Subgroup Model) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 8 := by
  classical
  by_cases h : ∃ x : E, (x : Model) ∉ centralTwo ⊔ transpositionSubgroup
  · obtain ⟨x, hx⟩ := h
    exact (elementary_card_le_commuting E x).trans
      (noncentral_bound x (elemPow_eq_one_of_isElementaryAbelian (x : Model) x.property)
        (fun hi => hx ((mem_centralTwo_sup_transposition x).mpr hi)))
  · have hc : E ≤ centralTwo ⊔ transpositionSubgroup := by
      intro x hx
      by_contra hn
      exact h ⟨⟨x, hx⟩, hn⟩
    have hcard : Nat.card ↥(centralTwo ⊔ transpositionSubgroup) = 4 := by
      rw [← centralTranspositionEmbedding_range,
        ← Nat.card_congr (MonoidHom.ofInjective centralTranspositionEmbedding_injective).toEquiv]
      simp [E4, C2]
    exact (Subgroup.card_le_of_le hc).trans (by omega)

theorem elementary_le_natural_of_eight_le (E : Subgroup Model)
    [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) : E ≤ natural := by
  intro x hx
  by_contra hn
  have hc := (elementary_card_le_commuting E ⟨x, hx⟩).trans
    (outside_bound x (elemPow_eq_one_of_isElementaryAbelian x hx)
      (fun h => hn ((mem_natural x).mpr h)))
  omega
end AlternatingSix.ShadowLocal.Holomorph

namespace AlternatingSix.ShadowLocal
open Identification

/-- Elementary two-subgroups of the actual automorphism group have order at
most eight; attaining eight places them in the permutation-induced S₆. -/
theorem elementary_card_and_placement (E : Subgroup AutA6) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 8 ∧ (8 ≤ Nat.card E → E ≤ natural) := by
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let e := sylowEquiv P
  let F := (E.subgroupOf (P : Subgroup AutA6)).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (E.subgroupOf (P : Subgroup AutA6)) :=
    IsElementaryAbelian.subgroupOf hEP
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hcard : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv
  refine ⟨hcard ▸ Holomorph.elementary_card_le_eight F, ?_⟩
  intro hE x hx
  have hF := Holomorph.elementary_le_natural_of_eight_le F (hcard.symm ▸ hE)
  have hxF : e.symm ⟨x, hEP hx⟩ ∈ F := mem_map_of_mem _ hx
  have hxN := mem_map_of_mem e.toMonoidHom (hF hxF)
  rw [sylowEquiv_natural P] at hxN
  change (e (e.symm ⟨x, hEP hx⟩) : AutA6) ∈ natural at hxN
  simpa only [MulEquiv.apply_symm_apply] using hxN

/-- The two-rank bound expressed as elementary subgroup order. -/
theorem elementary_card_le_eight (E : Subgroup AutA6) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 8 := (elementary_card_and_placement E).1

/-- Rank-three elementary subgroups induce natural permutations. -/
theorem elementary_le_natural_of_eight_le (E : Subgroup AutA6)
    [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) : E ≤ natural :=
  (elementary_card_and_placement E).2 hE

end AlternatingSix.ShadowLocal
