module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
public import FeitThompson.FinalTheorem
/-!
# A component with odd centralizer

Every other component would be a nontrivial perfect subgroup of the odd
centralizer, contradicting the odd-order theorem. Hence the component is
normal, and its centralizer is exactly the odd core. A perfect actor already
inside the component-centralizer product then lies in the component itself.

Source: the normality and residual-placement steps in Aschbacher--Smith
4.4.10--11, printed p.621, after the specialized odd-centralizer argument.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G:Type*} [Group G] [Finite G]
/-- Odd centralizer makes the component unique and therefore normal. -/
theorem IsComponent.normal_of_odd_centralizer
    {K:Subgroup G} (hK:IsComponent G K) (ho:Odd (Nat.card (centralizer (K:Set G)))) : K.Normal := by
  have hu (D:Subgroup G) (hD:IsComponent G D):D=K:=by
    by_contra hn
    have hDC:D≤centralizer (K:Set G):=commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne hK hn)
    let :IsQuasisimple D:=hD.2
    let :IsSimpleGroup (D⧸center D):=IsQuasisimple.simple
    let :Nontrivial D:=(QuotientGroup.mk'_surjective (center D)).nontrivial
    exact Group.IsPerfect.not_isSolvable D
      (_root_.odd_order_theorem D (ho.of_dvd_nat (card_dvd_of_le hDC)))
  exact normal_iff_map_conj_eq.mpr (fun g=>hu _ (hK.map_conj g))

/-- The actual odd component centralizer is the entire odd core. -/
theorem IsComponent.centralizer_eq_oddCore_of_odd_centralizer
    {K:Subgroup G} (hK:IsComponent G K) (ho:Odd (Nat.card (centralizer (K:Set G)))) :
    centralizer (K:Set G)=pPrimeCore 2 G := by
  let :K.Normal:=hK.normal_of_odd_centralizer ho
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,ho.coprime_two_left⟩
  · let :Group.IsSolvable (pPrimeCore 2 G):=_root_.odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    exact le_centralizer_iff.mp (hK.le_centralizer_of_solvable_normal _)

/-- A perfect actor with inner action has no image in the odd centralizer. -/
theorem IsComponent.perfect_actor_le_of_odd_centralizer
    {K:Subgroup G} (hK:IsComponent G K) (ho:Odd (Nat.card (centralizer (K:Set G))))
    (F:Subgroup G) [Group.IsPerfect F] (hinner:F≤K⊔centralizer (K:Set G)) : F≤K := by
  let :K.Normal:=hK.normal_of_odd_centralizer ho
  let C:=centralizer (K:Set G)
  let q:=QuotientGroup.mk' K
  let :Group.IsSolvable C:=_root_.odd_order_theorem C ho
  let :Group.IsSolvable (C.map q):=Group.isSolvable_of_surjective (q.subgroupMap_surjective C)
  have hFQ:F.map q≤C.map q:=by
    have hh:=map_mono (f:=q) hinner
    rwa [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] at hh
  let :Group.IsSolvable (F.map q):=Group.isSolvable_of_isSolvable_injective (inclusion_injective hFQ)
  let :Group.IsPerfect (F.map q):=Group.IsPerfect.map _
  have hb:F.map q=⊥:=by
    by_contra hn
    let :Nontrivial (F.map q):=(nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (F.map q) inferInstance
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
end Theory.GroupTheory
