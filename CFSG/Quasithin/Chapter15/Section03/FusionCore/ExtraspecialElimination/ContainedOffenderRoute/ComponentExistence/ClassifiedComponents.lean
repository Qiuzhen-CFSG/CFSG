module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.CubicTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Elimination

/-!
# Constructing components in the nonsolvable source alternatives

For B.5.6(1), take the literal generalized Fitting subgroup of J*, even
when J* is a proper extension of it. Its ambient image is normal in H*,
so its orbit has one member. For the two-factor alternatives, the proved
residual-factor construction supplies a modeled quasisimple component
with at most two H*-conjugates. The only exception is the actual S₃ × S₃
pair, already excluded by the compatible module data. The hyperplane
case always supplies its first SL₃(2) component.

Each component receives a proved noncentral cubic and is lifted inside
the original J. The theta and residual-normalizer argument gives outside
placement and L = [L,Y₀]. These are the nonsolvable branches of the
exhaustive assembly in `ComponentExistence`; no kernel absorption is used.
Source: Aschbacher–Smith, B.5.6(1),(3),(5), printed p.105, and
15.3.49(i), pp.1143–1144 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ComponentReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

omit [Finite G] in
private theorem starSpan_normal : (starImage H (localSpan d.selected.carrier H)).Normal :=
  (localSpan_normal d.selected.carrier H d.selected.le_local).map _
    (QuotientGroup.mk'_surjective _)

/-- The proper symmetric and G₂ extensions are handled by F*(J*),
without identifying the whole actor J* with its component. -/
theorem exists_of_generalizedFitting_model
    (hq : IsQuasisimple (generalizedFitting (starImage H (localSpan d.selected.carrier H))))
    (hm : QuasisimpleModel (generalizedFitting (starImage H (localSpan d.selected.carrier H)))) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  let := starSpan_normal d
  let := hq
  obtain ⟨hB, _, _, ho⟩ := ProductComponents.generalizedFitting_component
    (starImage H (localSpan d.selected.carrier H)) hq
  obtain ⟨x, hx, hn⟩ := noncentral_cubic_of_quasisimpleModel hm
  exact exists_of_star_component d _ hB (by rw [ho]; decide) x hx hn

/-- Every compatible two-factor source case has an outside component;
the all-solvable pair is excluded using its actual module decomposition. -/
theorem exists_of_twoFactorCase (c : TwoFactorCase (starAction d)) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  let := starSpan_normal d
  obtain ⟨B, hB, hq, hm, ho⟩ := ProductComponents.exists_component
    (starImage H (localSpan d.selected.carrier H)) c.product.equiv.symm
    c.firstModel c.secondModel (by
      rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
      exact SolvableProduct.not_two_symmetricThree d c e₁ e₂)
  let := hq
  obtain ⟨x, hx, hn⟩ := noncentral_cubic_of_componentModel hm
  exact exists_of_star_component d B hB ho x hx hn

/-- The hyperplane alternative supplies the first SL₃(2) component,
regardless of the second factor's natural or repeated-natural case. -/
theorem exists_of_hyperplaneCase (c : HyperplaneCase (starAction d)) :
    ∃ L : Subgroup G, OutsideComponent H M Y0 d.selected.carrier L := by
  let := starSpan_normal d
  obtain ⟨hB, hq, hm, ho⟩ := ProductComponents.hyperplane_first_component
    (starImage H (localSpan d.selected.carrier H)) c.product.equiv.symm c.firstEquiv
    (c.secondCase.factorModel (starAction d))
  let := hq
  obtain ⟨x, hx, hn⟩ := noncentral_cubic_of_componentModel hm
  exact exists_of_star_component d _ hB ho x hx hn

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
