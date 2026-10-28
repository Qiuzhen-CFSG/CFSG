module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Geometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Extraspecial
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneActorTransport
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.OddCore.Preparation

/-!
# Ordinary-component exclusion for every escaping G₂ cover hyperplane

The exact two-orbit model theorem supplies either a faithful exponent-three
actor of order 27 or a cubic-normalizing mover. The first makes the ambient
hyperplane centralizer three-prime, contradicting the actual component models.
In the second, symmetric comparison identifies a component and its conjugate
inside the same codimension-two centralizer, forcing it to centralize V.

All model and source premises are discharged. The conclusion is uniform over
every escaping hyperplane, exactly as required by the odd-core argument and
final ambient-centralizer assembly.
Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
open Chapter12.Section02 ChapterE ChapterB.QuasisimpleSource Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary-component branch of 12.4.8, uniformly over its actual escaping
hyperplanes. No model, actor or comparison premise remains. -/
theorem cover_components_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥) : OddCore.ComponentsExcluded V := by
  intro U hUV hcor hescape K hK
  rcases exists_cover_hyperplane_component_actors h D structural e hne hUV hcor hescape with
    ⟨Y,_,_,hcard,hpow,hYN,hdisjoint⟩ | ⟨x,l,hxL,hx,hxU,hxC,hlL,hlX,hm⟩
  · have c := (cover_localData h D structural e hne hUV hcor hescape).1
    exact c.no_component_of_faithful_twentySeven Y hYN hcard
      (fun y => Subtype.ext (hpow y y.property)) hdisjoint.eq_bot hK
  · exact cover_component_false_of_mover h D structural e hne hUV hcor hescape hK
      (D.normalizes hxL) hx hxU hxC (D.normalizes hlL) hlX hm

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
