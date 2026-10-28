module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Selection
public import Theory.Quasithin.ComponentPerfectAction
public import FeitThompson.FinalTheorem

/-!
# The original residual and chosen module normalize the detected component

The odd-order theorem makes every component even. The elementary
quasithin orbit bound then makes its normalizer contain the perfect
residual L_A. The same is true of V=[V,L_A]. Applied to the actual
component detected outside N(L), the component commutator dichotomy
therefore proves [K,V]=K. All maps stay inside the original N(A).

Source: Aschbacher--Smith4.4.9--10, p.621. This proves the normalization
needed there without assuming the sharper orbit classification of A.3.8.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- Both original actors normalize every component of the odd normalizer. -/
theorem chosen_oddNormalizer_component_normalization
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A))
    (hAV:A≤centralizer (V:Set G))
    (K:Subgroup (normalizer (A:Set G))) (hK:IsComponent (normalizer (A:Set G)) K) :
    (normalizer (K:Set (normalizer (A:Set G)))).index≤3 ∧
    (oddActorResidual L A).subgroupOf (normalizer (A:Set G))≤
      normalizer (K:Set (normalizer (A:Set G))) ∧
    V.subgroupOf (normalizer (A:Set G))≤normalizer (K:Set (normalizer (A:Set G))) := by
  let N:=normalizer (A:Set G)
  let F:=oddActorResidual L A
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN:V≤N:=(le_centralizer_iff.mp hAV).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,he,_,_⟩:=chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
  let :Group.IsPerfect F:=oddActorResidual_isPerfect L A
  let :Group.IsPerfect (F.subgroupOf N):=Group.IsPerfect.ofSurjective
    (f:=(subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  have heN:V.subgroupOf N=⁅V.subgroupOf N,F.subgroupOf N⁆:=by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact he
  let :IsQuasisimple K:=hK.2
  let :IsSimpleGroup (K⧸center K):=IsQuasisimple.simple
  let :Nontrivial K:=(QuotientGroup.mk'_surjective (center K)).nontrivial
  have heven:2∣Nat.card K:=by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable K
      (_root_.odd_order_theorem K (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hn)))
  have hqt:=h.simpleQTKE.quasithin.subgroup N
  exact ⟨hK.normalizer_index_le_three_of_quasithin hqt heven,
    hK.perfect_commutator_normalizes_of_quasithin hqt heven (F.subgroupOf N) (V.subgroupOf N) heN⟩

/-- The source data produce a component outside M with full V-commutator. -/
theorem chosen_oddNormalizer_exists_full_component_action
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
    (A:Subgroup G) [IsMulCommutative A] (hne:A≠⊥)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G)) :
    ∃K:Subgroup (normalizer (A:Set G)),
      IsComponent (normalizer (A:Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A:Set G))⁆=K ∧
      ¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G) ∧
      pCore 2 K=⊥ ∧ IsQuasithin K ∧ κ (K⧸center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A:Set G))≤
        normalizer (K:Set (normalizer (A:Set G))) ∧
      V.subgroupOf (normalizer (A:Set G))≤normalizer (K:Set (normalizer (A:Set G))) := by
  obtain ⟨K,hK,hm,houtK,hcore,hqt,hclass⟩:=chosen_oddNormalizer_exists_moved_component
    h D hcard A hne hAN hcomm hodd hAV hunique hout
  obtain ⟨_,hFK,hVK⟩:=chosen_oddNormalizer_component_normalization h D A hAN hcomm hodd hAV K hK
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hVK hm,houtK,hcore,hqt,hclass,hFK,hVK⟩
end CFSG.Quasithin.Chapter4.Section04
