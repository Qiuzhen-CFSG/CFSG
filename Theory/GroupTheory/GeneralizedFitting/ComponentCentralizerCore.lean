module
public import Theory.GroupTheory.GeneralizedFitting.MovedComponentOutside
/-!
# Prime-core freeness of a component centralizer

If O_p(G)=1, the p-core of a component centralizer commutes with F(G),
since F(G) has order prime to p. It also commutes with the original component
and all the other components. Generalized-Fitting detection therefore makes
that p-core trivial. No normality of the component in G is assumed.

Source application: the centralizer step in Aschbacher--Smith 4.4.10(3),
printed p.621.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G:Type*} [Group G] [Finite G]
/-- Trivial ambient prime core passes to the actual centralizer of any component. -/
theorem IsComponent.centralizer_pCore_eq_bot_of_pCore_eq_bot
    {K:Subgroup G} (hK:IsComponent G K) (p:ℕ) [Fact p.Prime]
    (hcore:pCore p G=⊥) : pCore p (centralizer (K:Set G))=⊥ := by
  let C:=centralizer (K:Set G)
  let R:=fittingSubgroup G
  let P:=C.pCoreIn p
  have hRC:R≤C:=le_centralizer_iff.mp (hK.le_centralizer_of_solvable_normal R)
  have hcop:Nat.Coprime p (Nat.card (R.subgroupOf C)):=by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv]
    exact Nat.Coprime.of_dvd_right (card_dvd_of_le
      (fitting_le_pPrimeCore_of_pCore_eq_bot p hcore)) pPrimeCore_coprime_card
  have hd:Disjoint (pCore p C) (R.subgroupOf C):=by
    obtain ⟨n,hn⟩:=(pCore_isPGroup (p:=p) (G:=C)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hcop.pow_left n
  have hf:P≤centralizer (R:Set G):=by
    have he:⁅pCore p C,R.subgroupOf C⁆=⊥:=le_bot_iff.mp
      ((commutator_le_inf _ _).trans hd.le_bot)
    have hh:=congrArg (Subgroup.map C.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hRC,Subgroup.map_bot] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh
  have hb:P=⊥:=by
    by_contra hn
    obtain ⟨D,hD,hm⟩:=exists_component_moved_of_centralizes_fitting p P
      (isPGroup_pCoreIn p C) hn hcore hf
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    by_cases he:D=K
    · subst D
      exact le_centralizer_iff.mp (pCoreIn_le p C)
    · have hDC:D≤C:=commutator_eq_bot_iff_le_centralizer.mp
        (hD.commutator_eq_bot_of_ne hK he)
      let :Group.IsNilpotent (pCore p C):=pCore_isNilpotent
      have hc: D.subgroupOf C≤centralizer (pCore p C:Set C):=
        (hD.subgroupOf hDC).le_centralizer_of_solvable_normal (pCore p C)
      intro d hd x hx
      obtain ⟨w,hw,rfl⟩:=hx
      exact congrArg Subtype.val (hc (show (⟨d,hDC hd⟩:C)∈D.subgroupOf C from hd) w hw)
  exact ((pCore p C).map_eq_bot_iff_of_injective C.subtype_injective).mp hb
end Theory.GroupTheory
