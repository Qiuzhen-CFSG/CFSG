module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment.Field

/-!
# Containment of the contained-offender residual in the component closure

From `ReducedModels.Input`, the actual component section in B.5.5 gives
all component models. The A₇ and genuine hexacode-cover cases force Y₀
into L directly. Under noncontainment the remaining Lie case has a
solvable relative Sylow normalizer. Universal (j), the theta identity and
solvability of Y₀T give Borel control. The intrinsic torus and field
calculations then force the binary parameter.

At that parameter, the individual component Sylow normalizers are
self-normalizing and their outer groups have order prime to three.
These statements transport to every T-conjugate. Their commuting product
makes the whole relative Borel equal to T ∩ ⟨L^T⟩; this implies
centerlessness of the star closure. Theta generation makes the action
inner on each factor, hence on their whole join. The invariant projection
argument now proves Y₀ ≤ ⟨L^T⟩.

The only additional parameter is the exact universal earlier component-section
implication B.5.5(1)(iii)–(iv)/B.4.2. Its actual application hypotheses are
proved by `Input.component_sections`. The local inputs in `Input.placed`
retain the extraspecial alternative and residual from 15.3.7(2), the theta
identity 15.3.49(b), the actual U_H/Z action from 15.3.48, and the contained
best actor selected after 15.3.49(h). Its seed-normalizer condition is
15.3.46(5). Minimality and the separately supplied outside component prove
the replacement and universal (j). No extra Borel, inner-action,
whole-endpoint best-offender, or component-generation premise is used.
The supplied outside component is kept separate from its construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(k), printed pp.1143–1144; B.5.5, pp.104–105; A.3.18, pp.51–52.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup ComponentReduction ModelReduction BorelInner
open AutomorphismCollapse ModelSelection
universe u
variable {G : Type u} [Group G] [Finite G]

namespace Containment
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z E upper : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- Containment with the original ambient Sylow subgroup explicitly marked. -/
theorem y_le_closure_sylow (sections : EarlierComponentSections κ) :
    Y0 ≤ localSpan L T := by
  by_contra hout
  obtain ⟨e, hmodel⟩ := lie_model d sections hout
  have hq := d.component.quasisimple
  let _ : Group.IsSolvable (relativeBorel L T) := borel_isSolvable d hq hmodel
  have he := exponent_eq_one d hout hmodel
  have hb : LieComponentModel (starImage H L) 1 := he ▸ hmodel
  have hB := borel_eq_of_component_self_normalizing d hq
    (AutomorphismCollapse.BinaryModels.binary_model_self_normalizing hb)
  have hc := closure_star_center_eq_bot_of_self_normalizing H L Y0 T
    d.replacement d.component.commutator_eq d.normalizes hB
  have hi := inner_star_of_factor_outer_three_free H M Y0 (localSpan L T)
    d.placed.theta_eq (conjugateFactors H L T) (conjugateFactors_sup d)
    (fun C hC D hD hne => conjugateFactors_commute d hq C D hC hD hne)
    (fun C hC => (conjugateFactors_properties d C hC).2.2.1) (by
      intro C hC
      obtain ⟨f⟩ := (conjugateFactors_properties d C hC).2.2.2
      rw [← Nat.card_congr (MulAut.outerCongr f).toEquiv]
      exact AutomorphismCollapse.BinaryModels.binary_model_outer_three_free hb)
  exact hout (d.y_le_closure_of_inner hc hi)

end Containment

namespace Input
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- Source 15.3.49(k) for the contained-offender route, conditional only on
its enumerated earlier component-section implication and the published Input. -/
theorem y_le_closure (sections : EarlierComponentSections κ) : Y0 ≤ localSpan L T := by
  have d' : Input κ H M Y V Y0 d.sylow ZS Z E L upper := d.sylow_eq.symm ▸ d
  simpa only [d.sylow_eq] using Containment.y_le_closure_sylow d' sections

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
