module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ThreeSubgroups

/-!
# Perfect groups acting through a simple two-core quotient

A normal subgroup of a finite perfect group with simple quotient modulo its
2-core either lies in that core or is the whole group. Consequently an actor
with nontrivial action on that quotient generates the perfect group by
commutators. If the actor centralizes a normalized section Q/U, the
three-subgroups lemma makes the perfect group centralize Q/U as well.
All normalizers are relative to the displayed ambient subgroups.

Source application: Aschbacher--Smith, 12.9.9(1), printed p.863 of
`refs/quasithin.pdf`, with K=K₁^g, A=V, Q=O₂(G₁)^g and U=U^g.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem normal_le_twoCore_or_eq_top
    [Group.IsPerfect G] [IsSimpleGroup (G ⧸ pCore 2 G)]
    (D : Subgroup G) [D.Normal] : D ≤ pCore 2 G ∨ D = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (D.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases (inferInstance : (D.map q).Normal).eq_bot_or_eq_top with hb | ht
  · left
    simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hb
  · right
    have hsup : D ⊔ pCore 2 G = ⊤ := by
      have hm := congrArg (comap q) ht
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
    have hp := isPGroup_quotient_of_sup_eq_top D (pCore 2 G) pCore_isPGroup hsup
    let : Group.IsNilpotent (G ⧸ D) := hp.isNilpotent
    apply top_unique
    simpa only [solvableResidual_eq_top] using solvableResidual_le_of_solvable_quotient D

/-- Nontrivial action on a simple two-core quotient generates a perfect group. -/
theorem commutator_eq_of_perfect_simple_core (K A : Subgroup G)
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hAK : A ≤ normalizer (K : Set G))
    (hmoves : ¬ ⁅K,A⁆ ≤ K.pCoreIn 2) : ⁅K,A⁆ = K := by
  let D := ⁅K,A⁆
  have hDK : D ≤ K := le_normalizer_iff_commutator_le_left.mp hAK
  let : (D.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDK).mpr (normalizer_commutator_ge_left K A)
  rcases normal_le_twoCore_or_eq_top (D.subgroupOf K) with hc | ht
  · apply (hmoves _).elim
    have hm := map_mono (f := K.subtype) hc
    rwa [map_subgroupOf_eq_of_le hDK] at hm
  · have hm := congrArg (map K.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hDK, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- An actor centralizing a normal section forces the perfect group it moves
to centralize the same section. All normality assumptions are relative. -/
theorem commutator_le_of_perfect_simple_core_action (K A Q U : Subgroup G)
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hAK : A ≤ normalizer (K : Set G))
    (hmoves : ¬ ⁅K,A⁆ ≤ K.pCoreIn 2)
    (hKQ : K ≤ normalizer (Q : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hAU : A ≤ normalizer (U : Set G))
    (hQU : Q ≤ normalizer (U : Set G))
    (hAQ : ⁅A,Q⁆ ≤ U) : ⁅K,Q⁆ ≤ U := by
  have hgen := commutator_eq_of_perfect_simple_core K A hAK hmoves
  rw [← hgen]
  apply commutator_commutator_le_of_rotate_of_le_normalizer hKU hAU hQU
  · exact (commutator_mono hAQ le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hKU)
  · exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hKQ) le_rfl).trans
      (by rwa [commutator_comm] at hAQ)

end Subgroup
