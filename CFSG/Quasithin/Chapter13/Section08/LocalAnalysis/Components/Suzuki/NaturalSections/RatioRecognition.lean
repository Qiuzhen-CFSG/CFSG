module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.FFExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.ModelComparisons

/-!
# Intrinsic representation reductions for the Suzuki branches

`not_ff_of_three_free` and its strong variant derive faithful FF exclusion
from the complete universal B.5 classification. Restriction to the actual
offender-generated subgroup supplies the generation hypothesis of B.5.3;
faithfulness, the trivial two-core and a finite SQTK cover all survive.

`natural_of_quadraticRatio_le_two` derives an actual natural-module
identification from the full universal B.4.2 and B.4.5 implications. The
complete B.4.5 case analysis leaves a natural Suzuki action or a generalized
Fitting subgroup of order divisible by three. The supplied Suzuki marking
excludes the latter, and Suzuki parameter rigidity identifies the parameter.
No assertion that the whole actor has order prime to three is needed here.
The resulting actor equivalence is constructed with its intertwiner;
`adjusted_marking_of_quadraticRatio_le_two` relates it to the initially
supplied marking by an automorphism of the concrete Suzuki group.

The re-exported model comparisons exclude the non-Suzuki F.9.18 cases.
The universal B.4/B.5 implications remain explicit earlier inputs; this
module proves their intrinsic consequences, leaving the ambient F.9.18
and natural-section assembly to its consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2/B.4.5,
pp.86–87; B.5.1/B.5.6, pp.99 and 105; F.9.18, pp.325–326. The natural
Suzuki module assertion is justified in K.3.6 and the paragraph preceding
K.3.5, p.457.
-/

@[expose] public section

open Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition

universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)
  {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
  (hB45 : SmallRatioSource.FullB45.{u,v} 𝒦)
  (hsqtk : IsSQTK 𝒦 D) (hfaith : Function.Injective ρ)
  (hquasi : IsQuasisimple (generalizedFitting D))
  (hirr : IsIrreducible (ρ.comp (generalizedFitting D).subtype))
  (hq : quadraticRatio ρ ≤ 2)
  {m : ℕ} (hm : 0 < m) (e : generalizedFitting D ≃* SuzukiMatrixGroup m)

include hB42 hB45 hsqtk hfaith hquasi hirr hq hm e

/-- A faithful finite binary SQTK action with quasisimple Suzuki generalized
Fitting subgroup and quadratic ratio at most two is natural on that subgroup.
The complete earlier classifications are the only source-theorem inputs.
`ActionEquiv` includes both the actor isomorphism and an equivariant linear
equivalence with the concrete natural module at the given parameter. -/
theorem natural_of_quadraticRatio_le_two :
    Nonempty (ActionEquiv (ρ.comp (generalizedFitting D).subtype) (natural m)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hyp : B4Hypotheses 𝒦 ρ := ⟨hsqtk, hfaith, hquasi, hirr⟩
  have h := SmallRatioSource.natural_or_three_of_full_classification ρ hB42 hB45 hyp hq
  exact exists_natural_with_parameter _ hm e
    (h.resolve_right (three_free_of_equiv_suzuki hm e))

/-- The same recognition with the adjustment to any prescribed marking
made explicit. Equivariance is proved for the constructed marking `α ∘ e`. -/
theorem adjusted_marking_of_quadraticRatio_le_two :
    ∃ α : MulAut (SuzukiMatrixGroup m),
      ∃ f : V ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)),
        ∀ g : generalizedFitting D, ∀ v,
          f (ρ g v) = natural m (α (e g)) (f v) := by
  obtain ⟨a⟩ := natural_of_quadraticRatio_le_two ρ hB42 hB45
    hsqtk hfaith hquasi hirr hq hm e
  refine ⟨e.symm.trans a.groupEquiv, a.linearEquiv, ?_⟩
  intro g v
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using a.intertwines g v

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
