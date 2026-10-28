module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Selection
public import Theory.GroupTheory.NormalizerAction

/-!
# The selected component's literal faithful action

The source group is X = KL₁V inside the original H. Its action on the
selected K-star factors through H → H/O₂(H), with kernel C_X(K-star).
The marking below records the resulting action, its exact kernel, and
the images of the original K, L₁ and V. It is an output specification;
the original-source construction is in NaturalSource.ComponentAction.

Identifying the image of K with Inn(K-star) gives an actual equivalence
with K-star/Z(K-star), rather than an unrelated simple-group label.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent
variable {G : Type*} [Group G] {E : Setup G} {H : Subgroup G}
  (c : E.SelectedComponent H)

/-- The original local product, before either quotient is taken. -/
noncomputable def localActor : Subgroup G := c.K ⊔ E.L₁ ⊔ E.V

/-- Results of the source action construction. None is a hypothesis on
the original chosen module or a component-selection assumption. -/
structure ActionMarking where
  local_le : c.localActor ≤ H
  component_normal : (c.K.subgroupOf c.localActor).Normal
  action : c.localActor →* MulAut (star H c.K)
  conjugation : ∀ (x : c.localActor) (k : star H c.K),
    (action x k : Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion local_le x) * k.val *
        (QuotientGroup.mk' (pCore 2 H) (inclusion local_le x))⁻¹
  kernel : action.ker = (centralizer (star H c.K : Set (Hstar H))).comap
    ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion local_le))
  component_image : (c.K.subgroupOf c.localActor).map action =
    MulAut.innerSubgroup (star H c.K)
  module_card : Nat.card ((E.V.subgroupOf c.localActor).map action) = 2
  residual_ne_bot : (E.L₁.subgroupOf c.localActor).map action ≠ ⊥
  residual_twoPerfect : IsPPerfect 2 ((E.L₁.subgroupOf c.localActor).map action)
  residual_three_dvd : 3 ∣ Nat.card ((E.L₁.subgroupOf c.localActor).map action)
  residual_centralizes : (E.L₁.subgroupOf c.localActor).map action ≤
    centralizer ((E.V.subgroupOf c.localActor).map action : Set (MulAut (star H c.K)))

namespace ActionMarking
variable {c} (a : c.ActionMarking)

/-- The actual quotient X/C_X(K-star), represented faithfully on K-star. -/
noncomputable def quotientEquiv : (c.localActor ⧸ a.action.ker) ≃* a.action.range :=
  QuotientGroup.quotientKerEquivRange a.action

theorem quotientEquiv_mk (x : c.localActor) :
    (a.quotientEquiv (QuotientGroup.mk' a.action.ker x) : MulAut (star H c.K)) =
      a.action x := rfl

/-- The source K-hat is the central quotient of the selected K-star. -/
noncomputable def componentQuotientEquiv :
    (star H c.K ⧸ center (star H c.K)) ≃*
      (c.K.subgroupOf c.localActor).map a.action :=
  (NormalizerAction.componentCentralQuotientEquiv (star H c.K)).trans
    (((NormalizerAction.componentImage (star H c.K)).equivMapOfInjective
      (NormalizerAction.action (star H c.K))
      (NormalizerAction.action_injective (star H c.K))).trans
        (MulEquiv.subgroupCongr
          ((NormalizerAction.action_map_componentImage (star H c.K)).trans a.component_image.symm)))

theorem componentQuotientEquiv_mk (k : star H c.K) :
    (a.componentQuotientEquiv (QuotientGroup.mk' (center (star H c.K)) k) :
      MulAut (star H c.K)) = MulAut.conj k := by
  ext b
  rfl

end ActionMarking
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent
