module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.Ordinary
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.CoveredSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original

/-!
# Assembly of the earlier residual input on the original component consumer

The ordinary branch is discharged from the original hypotheses. In the
covered branch, the original theta identity and the genuine L₀ normalizer
bound are also discharged, leaving exactly the two-group centralizer kernel
calculation of 13.3.7–9. The conditional assembly feeds the unchanged
whole-Fitting-residual consumer. It is not a proof of the covered source
theorem until that remaining assertion has been supplied.

Source: Aschbacher–Smith 13.3.9, printed p.887, and13.8.12–16, pp.950–952.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion SolvableExclusion.Residual
open Section03.PointResidualImage
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
include d h

/-- The source statement is reduced to the remaining covered centralizer
kernel calculation. Theta and the L₀ normalizer bound are discharged. -/
theorem source_of_covered_kernel
    (hkernel : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      ∀ J Y : Subgroup G, J ∈ Chapter1.HOutside G (T:Set G) (M:Set G) →
      Y ≤ J → IsPPerfect 2 Y → (Y.subgroupOf J).Normal →
      (∃v∈V₁, v∉V⊓centralizer (L:Set G) ∧ Y≤M⊓centralizer ({v}:Set G)) →
      IsPGroup 2 (Y⊓centralizer (V:Set G) : Subgroup G)) :
    Source1339 L (one L (T:Subgroup G) V₁) (plus L (T:Subgroup G) V₁) T M V V₁ := by
  rcases LocalFitting.quotient_models d with hm | hc
  · exact ordinary_source d h hm
  · obtain ⟨a⟩ := covered_flag_of_triple d hc
    exact source_covered_1339 d hc (theta_normalizer d h)
      (SolvableSource.covered_normalizer_source d h ⟨a.cover⟩) (hkernel hc)

/-- The ordinary original 13.8.14 consumer has no 13.3.9 source parameter.
The independently owned solvable-overgroup exclusion retains its original premise. -/
theorem ordinary_whole_residual
    (hm : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (hH : H∈Source.Hz (one L T V₁) T G₁ M)
    (hex : ∀ J:Subgroup G, one L T V₁⊔(T:Subgroup G)≤J → J≤G₁ →
      Group.IsSolvable J → J≤M) :
    Components.Fitting.ResidualAlternatives H L (one L T V₁) (plus L T V₁) :=
  LocalFitting.whole_residual d hH (ordinary_source d h hm) hex

/-- Conditional full assembly on the literal Fitting residual. This does not
assert that the earlier covered centralizer-kernel calculation is discharged. -/
theorem whole_residual_of_covered_kernel
    (hkernel : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      ∀ J Y : Subgroup G, J ∈ Chapter1.HOutside G (T:Set G) (M:Set G) →
      Y ≤ J → IsPPerfect 2 Y → (Y.subgroupOf J).Normal →
      (∃v∈V₁, v∉V⊓centralizer (L:Set G) ∧ Y≤M⊓centralizer ({v}:Set G)) →
      IsPGroup 2 (Y⊓centralizer (V:Set G) : Subgroup G))
    (hH : H∈Source.Hz (one L T V₁) T G₁ M)
    (hex : ∀ J:Subgroup G, one L T V₁⊔(T:Subgroup G)≤J → J≤G₁ →
      Group.IsSolvable J → J≤M) :
    Components.Fitting.ResidualAlternatives H L (one L T V₁) (plus L T V₁) :=
  LocalFitting.whole_residual d hH (source_of_covered_kernel d h hkernel) hex
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
