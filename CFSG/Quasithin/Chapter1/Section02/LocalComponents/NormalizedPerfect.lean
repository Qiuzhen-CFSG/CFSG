module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Normalized perfect groups in a Sylow local family

A perfect subgroup normalized by S is normal in its join with S. If its
quotient by O₂ is quasisimple, it is a C-component of that join. Its
nontrivial two-core is normalized by the join and supplies the remaining
local-family condition. Sylow containment is restricted from the given
ambient overgroup. No ambient component hypothesis on the subgroup is used.

Source: Aschbacher--Smith Definition 1.2.3, printed p.505; applied to
parabolic residuals in 15.1.20(3), printed p.1096.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- A normalized perfect group with quasisimple two-core quotient and nontrivial
core belongs to the literal local family relative to the given Sylow. -/
theorem mem_LIn_of_normalized_perfect {H S K : Subgroup G}
    (hS : IsSylowIn 2 S H) (hKH : K ≤ H) (hn : S ≤ normalizer (K : Set G))
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hcore : K.pCoreIn 2 ≠ ⊥) : K ∈ LIn H S := by
  have hSH : S ≤ H := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ map_subtype_le _
  let J := K ⊔ S
  let : (K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hn)
  let e := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : Group.IsPerfect (K.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp : IsPPerfect 2 (K.subgroupOf J) := by
    intro N hN hq
    let := hN
    let : Group.IsNilpotent ((K.subgroupOf J) ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hc : K.pCoreIn 2 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans le_sup_left)
    ((sup_le K.le_normalizer hn).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  exact ⟨hKH,isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : (K.subgroupOf J).Normal).isSubnormal hp,
    hS.restrict le_sup_right (sup_le hKH hSH),fun he => hcore (bot_unique (he ▸ hc))⟩

end CFSG.Quasithin.Chapter1
