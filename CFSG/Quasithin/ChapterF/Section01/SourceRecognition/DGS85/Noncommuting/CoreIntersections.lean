module
public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Two-core intersections at noncommuting critical endpoints

A normal Sylow two-subgroup captures the intersection of its overgroup
with any two-subgroup. Applied separately to the full local kernel and
the local centralizer, this proves the intersection identities and reverse
escape used at the start of DGS7.1. The kernel itself is never identified
with the two-core, and the ambient group need not be finite.

Source: DGS, *Groups and Graphs* (1985),7.1, printed p.126, using3.8(d)
and6.2(c,d). The source setup owner supplies those local Sylow premises.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- A normal Sylow subgroup captures the intersection with every two-group.
This does not identify the containing group with that Sylow subgroup. -/
theorem inf_eq_inf_of_normal_sylow
    (B N Q : Subgroup G) (hB : IsPGroup 2 B)
    (hQN : Q ≤ N) (hn : N ≤ normalizer (Q : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn Q N) : B ⊓ N = B ⊓ Q := by
  obtain ⟨S, hS⟩ := hS
  have he : (S : Subgroup N) = Q.subgroupOf N := by
    rw [← hS]
    change (S : Subgroup N) = ((S : Subgroup N).map N.subtype).comap N.subtype
    rw [comap_map_eq_self_of_injective N.subtype_injective]
  let : (Q.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hQN).mpr hn
  let : (S : Subgroup N).Normal := he.symm ▸ inferInstance
  let B' := (B ⊓ N).subgroupOf N
  have hp : IsPGroup 2 B' :=
    hB.to_inf_left.of_equiv (subgroupOfEquivOfLe (show B ⊓ N ≤ N from inf_le_right)).symm
  have hmax : (S : Subgroup N) ⊔ B' = (S : Subgroup N) :=
    S.is_maximal' (S.isPGroup'.to_sup_of_normal_left hp) le_sup_left
  have hBS : B' ≤ (S : Subgroup N) := hmax ▸ le_sup_right
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hxS := hBS (show (⟨x, hx.2⟩ : N) ∈ B' from hx)
    exact hS ▸ mem_map_of_mem N.subtype hxS
  · exact inf_le_inf_left B hQN

/-- The centralizer intersection in DGS7.1, from the actual normal Sylow
in the local centralizer supplied by6.2. -/
theorem inf_centralizer_eq_inf_core
    (L Q Z B : Subgroup G) (hB : IsPGroup 2 B) (hBL : B ≤ L)
    (hQL : Q ≤ L) (hQC : Q ≤ centralizer (Z : Set G))
    (hn : L ≤ normalizer (Q : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn Q (L ⊓ centralizer (Z : Set G))) :
    B ⊓ centralizer (Z : Set G) = B ⊓ Q := by
  have he := inf_eq_inf_of_normal_sylow B (L ⊓ centralizer (Z : Set G)) Q hB
    (le_inf hQL hQC) (inf_le_left.trans hn) hS
  simpa only [← inf_assoc, inf_of_le_left hBL] using he

/-- Noncommutation reverses escape from the full local kernel, while retaining
its distinction from the two-core. -/
theorem not_le_kernel_of_noncommuting
    (Z B U Q : Subgroup G) (hB : IsPGroup 2 B)
    (hQU : Q ≤ U) (hn : U ≤ normalizer (Q : Set G))
    (hS : Stellmacher.IsSylowSubgroupIn Q U)
    (hQC : Q ≤ centralizer (Z : Set G)) (hc : ⁅Z,B⁆ ≠ ⊥) : ¬ B ≤ U := by
  intro hBU
  have he := inf_eq_inf_of_normal_sylow B U Q hB hQU hn hS
  rw [inf_of_le_left hBU] at he
  have hBQ : B ≤ Q := he.le.trans inf_le_right
  apply hc
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  exact hBQ.trans hQC

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
