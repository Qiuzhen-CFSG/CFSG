module

public import Theory.GroupTheory.PerfectPGroupGeneration

/-!
# Commutator generation in the original local group

Apply the perfect-group Sylow theorem inside the original subgroup K,
then map the conclusion back through K.subtype. The supplied Sylow group
has ambient image SP; the source 14.7.72 equality S'=V≤U supplies its
commutator bound. Thus [P,K]U=P is proved before any indecomposability
claim about P/U.

The actual Sylow identification SP∈Syl₂(K) and perfectness of K remain
explicit preceding inputs to this algebraic step. The 14.7.73 source
assembly must construct them. No ambient quotient map is substituted for
the literal subgroup maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73, printed pp.1076–1077 (PDF pp.1093–1094).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

/-- Apply the perfect-cover obstruction inside the original K and return its ambient commutators. -/
theorem commutator_generation_of_source_sylow
    {G : Type*} [Group G] [Finite G]
    (K P S U : Subgroup G) [Group.IsPerfect K]
    [(P.subgroupOf K).Normal] [(U.subgroupOf K).Normal]
    (hPK : P ≤ K) (hSK : S ≤ K) (hUP : U ≤ P) (hP : IsPGroup 2 P)
    (R : Sylow 2 K) (hR : (R : Subgroup K).map K.subtype = S ⊔ P)
    (hS : ⁅S, S⁆ ≤ U) : ⁅P, K⁆ ⊔ U = P := by
  have hRS : (R : Subgroup K) = S.subgroupOf K ⊔ P.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hSK, map_subgroupOf_eq_of_le hPK, hR]
  have hp : IsPGroup 2 (P.subgroupOf K) :=
    hP.of_injective (subgroupOfEquivOfLe hPK).toMonoidHom
      (subgroupOfEquivOfLe hPK).injective
  have hs : ⁅S.subgroupOf K, S.subgroupOf K⁆ ≤ U.subgroupOf K := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hSK]
    exact hS
  have hh := normal_pGroup_commutator_generation
    (P.subgroupOf K) (U.subgroupOf K) (S.subgroupOf K)
    (fun _ hu => hUP hu) hp R hRS hs
  have hm := congrArg (Subgroup.map K.subtype) hh
  rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hPK,
    map_subgroupOf_eq_of_le (hUP.trans hPK), ← MonoidHom.range_eq_map,
    K.range_subtype] at hm
  exact hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
