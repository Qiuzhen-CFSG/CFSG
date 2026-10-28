module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.CharacteristicTwoCoreIndex
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Characteristic two in Sylow overgroups and subnormal subgroups

This module proves Aschbacher–Smith 1.1.3(1) and 1.1.4(2),(6),(7),
preserving the intrinsic cores and relative normality in their statements.
If H has nontrivial two-core and contains the fixed Sylow subgroup T,
extend H to a maximal two-local M. Condition (E) gives characteristic
two in M. The core of M lies in the core of H, so H inherits the same
centralizer bound. This proves (6), and (2) follows by normalizing the
specified nontrivial subgroup normal in T.

The subnormal assertion uses the general proved inheritance theorem.
For (7), the index bound inside a Sylow subgroup implies the same bound
inside the two-core, where the centralizer restriction argument applies.
The source's other inheritance and overgroup clauses remain separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 1.1.3 and 1.1.4, printed pp.500–501.
-/

public section

namespace CFSG.Quasithin.Chapter1
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- 1.1.3(1): a nontrivial subnormal subgroup of a member of He belongs to He.
Normality is relative to the indicated overgroup. -/
theorem lemma_1_1_3_1 {M N : Subgroup G} (hM : M ∈ He G)
    (_hN : N ≠ ⊥) (hNM : N ≤ M) (hn : (N.subgroupOf M).IsSubnormal) :
    N ∈ He G := by
  apply mem_He_iff.mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hNM)).mp
    (subnormal_core_selfCentralizing (mem_He_iff.mp hM) (N.subgroupOf M) hn)

/-- 1.1.4(6): every overgroup of T with nontrivial two-core belongs to He.
Only condition (E) at the specified Sylow subgroup is required. -/
theorem lemma_1_1_4_6 (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T) :
    HOver G (T : Set G) ⊆ He G := by
  intro H hH
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    apply hH.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨M, hM, hHM⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hc := centralizer_pCore_le_of_sylow_le (T.subtype (hTH.trans hHM))
    (H.subgroupOf M) (fun x hx => hTH hx) (hE M hM (hTH.trans hHM))
  exact mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hHM)).mp hc)

/-- The final assertion of 1.1.4(2): two-locals containing T belong to He. -/
theorem twoLocal_mem_He_of_sylow_le (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {M : Subgroup G}
    (hM : IsTwoLocal M) (hTM : (T : Subgroup G) ≤ M) : M ∈ He G :=
  lemma_1_1_4_6 T hE ⟨mem_H_of_isTwoLocal hM, hTM⟩

/-- 1.1.4(2): a nontrivial subgroup normal in T has its ambient normalizer in He. -/
theorem lemma_1_1_4_2 (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {U : Subgroup G} (hne : U ≠ ⊥) (hUT : U ≤ (T : Subgroup G))
    (hn : (U.subgroupOf (T : Subgroup G)).Normal) : U ∈ S2e G := by
  have hp : IsPGroup 2 U := T.isPGroup'.to_le hUT
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUT).mp hn
  exact ⟨hne, hp, twoLocal_mem_He_of_sylow_le T hE ⟨U, hne, hp, rfl⟩ hTN⟩

/-- 1.1.4(7): intersecting a Sylow two-subgroup in index at most two suffices
to inherit membership in He. No normality of N in M is assumed. -/
theorem lemma_1_1_4_7 {M N : Subgroup G} (hM : M ∈ He G)
    (S : Sylow 2 M) (_hN : N ≠ ⊥) (hNM : N ≤ M)
    (hi : (N.subgroupOf M).relIndex (S : Subgroup M) ≤ 2) : N ∈ He G := by
  apply mem_He_iff.mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hNM)).mp
    (centralizer_pCore_le_of_sylow_relIndex_le_two (mem_He_iff.mp hM) S
      (N.subgroupOf M) hi)

end CFSG.Quasithin.Chapter1
