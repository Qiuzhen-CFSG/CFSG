module
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.Quasithin.Rank

/-!
# Odd-normalizer reductions after genuine covering uniqueness

The actual residual uniqueness supplied by the earlier pushing-up source
controls N(V) and forces O2(N(B))=1 for an outside odd normalizer. Separately,
simplicity makes a nontrivial abelian actor normalizer proper, quasithin and
a K-group. Strong quasithinness is not inferred.
Source: Aschbacher--Smith4.4.6(3),4.4.7(1), printed pp.619--620.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- Once the genuine earlier pushing-up theorem establishes uniqueness for
L_B, its first two odd-local reductions follow on the original subgroups. -/
theorem oddNormalizer_reduction_of_cover_uniqueness
    {T:Sylow 2 G} {L V M:Subgroup G}
    (D:Chapter12.Section02.ChosenModule T L V) (B:Subgroup G)
    (hunique:UniqueMaximalOvergroup (oddActorResidual L B) M)
    (hout:¬ normalizer (B:Set G)≤M) :
    normalizer (V:Set G)≤M ∧ pCore 2 (normalizer (B:Set G))=⊥ := by
  have hN:oddActorResidual L B≤normalizer (V:Set G):=
    ((oddActorResidual_le L B).trans inf_le_left).trans D.normalizes
  let :=D.elementary
  refine ⟨normalizer_le_of_unique_maximalTwoLocal hunique.2.2
    (IsElementaryAbelian.isPGroup 2 V) D.ne_bot hN,?_⟩
  have hI:oddActorResidual L B≤normalizer (B:Set G):=
    ((oddActorResidual_le L B).trans inf_le_right).trans (centralizer_le_normalizer _)
  have hh:=Theory.GroupTheory.twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    (oddActorResidual L B) (normalizer (B:Set G)) M hunique.2.2 hout
  rwa [sup_eq_right.mpr hI] at hh
end CFSG.Quasithin.Chapter4.Section04

namespace CFSG.Quasithin.Chapter4.Section04
open Subgroup
variable {G:Type*} [Group G] [Finite G]

/-- A nontrivial abelian actor in the original simple group has a proper
normalizer, so its K-group hypothesis is inherited from the source. -/
theorem oddNormalizer_properQTK {K:GroupClass} (h:IsSimpleQTKE K G)
    (B:Subgroup G) [IsMulCommutative B] (hB:B≠⊥) :
    normalizer (B:Set G)≠⊤ ∧ IsQuasithin (normalizer (B:Set G)) ∧
      IsKGroup K (normalizer (B:Set G)) := by
  let : IsSimpleGroup G:=h.simple
  have hn:normalizer (B:Set G)≠⊤:=by
    intro he
    let : B.Normal:=normalizer_eq_top_iff.mp he
    have hb:B=⊤:=((inferInstance:B.Normal).eq_bot_or_eq_top).resolve_left hB
    apply h.nonabelian
    constructor
    constructor
    intro a b
    have ha:a∈B:=hb ▸ mem_top a
    have hb':b∈B:=hb ▸ mem_top b
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a,ha⟩:B) ⟨b,hb'⟩)
  exact ⟨hn,h.quasithin.subgroup _,h.properK _ hn⟩
end CFSG.Quasithin.Chapter4.Section04
