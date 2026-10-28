module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Mathlib.Order.Preorder.Finite

/-!
# The source ordering and exclusion of the centralizer partner

Every original maximal two-local overgroup normalizes the nontrivial
elementary module V(M), hence equals its normalizer. The finite partial
order of A.5 therefore gives an ordering-maximal overgroup of every M.
A unique ordering maximum dominates the whole family.

If that maximum were Mc, the centralizer of each V(M) would lie in Mc
because V(M) contains Ω₁Z(T). The literal ordering factorization would
force every maximal two-local overgroup into Mc, contradicting the
original hypothesis that there are at least two.

This proves Aschbacher–Smith 14.1.9, printed p.977. It does not assume
empty Lf, a characteristic pair, or the later choice of Mf.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem centralInvolutions_ne_bot_of_maximal_local
    (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) : centralInvolutions T ≠ ⊥ := by
  have hcore : M.pCoreIn 2 ≠ ⊥ := Chapter1.mem_H_of_isTwoLocal hM.1.1
  have hCT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.2] using
      pCoreIn_le_sylow M (T.subtype hM.2)
  have hT : (T : Subgroup G) ≠ ⊥ := fun h => hcore (bot_unique (hCT.trans_eq h))
  let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hT
  have h := Subgroup.omega_center_ne_bot T.isPGroup'
  intro hz
  exact h ((Subgroup.map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp hz)

theorem maximal_local_normalizer_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    M ∈ normalizerOvergroups T := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let := localModule_elementary_from_source hG T hH
  have hV : localModule T M ≠ ⊥ := fun h =>
    centralInvolutions_ne_bot_of_maximal_local T hM
      (bot_unique ((le_conjugateSpanBy _ _).trans_eq h))
  have hN : M ≤ normalizer (localModule T M : Set G) := le_normalizer_conjugateSpanBy _ _
  have hn : IsTwoLocal (normalizer (localModule T M : Set G)) :=
    ⟨localModule T M, hV, IsElementaryAbelian.isPGroup 2 _, rfl⟩
  exact ⟨hH, le_antisymm hN (hM.1.2 hn hN)⟩

theorem ordering_le_maximal_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {K : Subgroup G} (hK : K ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    ∃ M : Subgroup G, IsOrderingMaximal T M ∧ OrderingLE T K M := by
  let A := {H : Subgroup G // H ∈ normalizerOvergroups T}
  let : LE A := (orderingPartialOrder T).toLE
  let : LT A := (orderingPartialOrder T).toLT
  let : Preorder A := (orderingPartialOrder T).toPreorder
  let : PartialOrder A := orderingPartialOrder T
  let k : A := ⟨K, maximal_local_normalizer_from_source hG T hK⟩
  obtain ⟨m, hkm, hm⟩ := Finite.exists_le_maximal
    (p := fun a : A => a.val ∈ maximalLocals T) (a := k) hK
  refine ⟨m.val, ⟨hm.1, ?_⟩, hkm⟩
  intro L hL hmL
  let l : A := ⟨L, maximal_local_normalizer_from_source hG T hL⟩
  have hml : m ≤ l := hmL
  have hlm : l ≤ m := hm.2 (show l.val ∈ maximalLocals T from hL) hml
  exact congrArg Subtype.val (le_antisymm hlm hml)

theorem unique_ordering_maximal_dominates_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M K : Subgroup G} (hunique : ∀ L, IsOrderingMaximal T L → L = M)
    (hK : K ∈ maximalTwoLocalOvergroups (T : Subgroup G)) : OrderingLE T K M := by
  obtain ⟨L, hL, hKL⟩ := ordering_le_maximal_from_source hG T hK
  exact hunique L hL ▸ hKL

theorem unique_ordering_maximal_ne_partner_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G}
    (hM : IsOrderingMaximal T M)
    (hmax : ∀ L, IsOrderingMaximal T L → L = M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) : M ≠ Mc := by
  intro he
  subst M
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) := by
    rw [hunique]
    exact Set.mem_singleton Mc
  have hall (K : Subgroup G) (hK : K ∈ maximalTwoLocalOvergroups (T : Subgroup G)) : K = Mc := by
    have hKM := unique_ordering_maximal_dominates_from_source hG T hmax hK
    have hle : K ≤ Mc := by
      intro x hx
      obtain ⟨a, ha, c, hc, rfl⟩ := hKM x hx
      exact Mc.mul_mem ha.2 (hMc.2 (centralizer_le (le_conjugateSpanBy _ _) hc.2))
    exact le_antisymm hle (hK.1.2 hMc.1.1 hle)
  have heq : maximalTwoLocalOvergroups (T : Subgroup G) = {Mc} := by
    ext K
    constructor
    · intro hK
      exact Set.mem_singleton_iff.mpr (hall K hK)
    · intro hK
      exact Set.mem_singleton_iff.mp hK ▸ hM.1
  rw [heq, Set.ncard_singleton] at hmany
  omega
end CFSG.Quasithin.Chapter15.Section03.InitialSource
