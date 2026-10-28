module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification.Components
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve.Preparation

/-!
# The component enumeration before the Borel exclusions

For the actual actor J* = ⟨A^H⟩*, the supplied component generation makes
J* perfect. The section action on U_H/Z satisfies every B.5.3 hypothesis,
with its literal finite SQTK cover and quotient equivalence. Applying the
complete FF alternatives and the perfect-actor component analysis proves
ordinary quasisimplicity of the selected relative component and identifies
its concrete carrier. The existing star quotient equivalence transports
quasisimplicity back to L/O₂(L).

`sourceSetup_alternative` retains the full representation conclusion for
later module arguments. The classification input is the exact universal
B.5.1/B.5.6 interface for the selected class κ; these universal appendix
results are not proved here. No component-model conclusion, exceptional
exclusion, or restriction to the binary field is added to `SourceSetup`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2, p.86;
B.5.1 and B.5.3–6, pp.99–105; proof of 15.3.49(i)–(k), pp.1143–1144.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- Apply the complete universal classification to the literal faithful
section action. All representation clauses remain available to consumers. -/
theorem sourceSetup_alternative (h : CompleteClassificationInput.{u,u} κ) :
    SourceAlternative (d.action.representation.comp (starImage H (localSpan A H)).subtype) := by
  have hyp := BinaryModels.ModelSieve.starSpanFFHypothesis
    H ZS Z A d.action d.sqtk d.actor_le d.best
  exact h.general _ _ _ hyp.1

/-- The selected component has its intrinsic quasisimple two-core quotient
and one of the actual B.5.5(1iv) carriers. Component generation, not an
additional quasisimplicity assumption, supplies the perfect FF actor. -/
theorem sourceSetup_component_classification (h : CompleteClassificationInput.{u,u} κ) :
    IsQuasisimple (L ⧸ pCore 2 L) ∧ ComponentModel (starImage H L) := by
  let : Group.IsPerfect (starImage H (localSpan A H)) :=
    BinaryModels.ModelSieve.starSpan_isPerfect H A d.actor_le d.component_generation
  obtain ⟨hq, hm⟩ := component_classification_of_source_alternative _
    (sourceSetup_alternative d h) (star_isCComponent_in_span d)
  let e := subgroupOfEquivOfLe
    (show starImage H L ≤ starImage H (localSpan A H) from
      map_mono (comap_mono d.component_le))
  let := hq
  have hstar : IsQuasisimple (starImage H L) := IsQuasisimple.of_mulEquiv e
  exact ⟨(component_quotient_quasisimple_iff d).mpr hstar,
    componentModel_of_equiv e.symm hm⟩

/-- The intrinsic quotient part of the classification. -/
theorem sourceSetup_component_quotient_quasisimple (h : CompleteClassificationInput.{u,u} κ) :
    IsQuasisimple (L ⧸ pCore 2 L) := (sourceSetup_component_classification d h).1

/-- The concrete carrier part, prior to exceptional or larger-field exclusions. -/
theorem sourceSetup_component_model (h : CompleteClassificationInput.{u,u} κ) :
    ComponentModel (starImage H L) := (sourceSetup_component_classification d h).2

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
