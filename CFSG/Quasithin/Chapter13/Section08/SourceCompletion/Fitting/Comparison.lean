module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Source
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Covered

/-!
# The actual Fitting residual in the covered comparison

The source Fitting-preimage residual is identified with the same embedded
two-residual used in the local component calculation. Consequently the
covered 13.8.21(1) comparison consumes the proved 13.8.14 alternative directly.
No Fitting alternative, cubic order, solvability of L1 T, or component-orbit
assertion is a premise. The independent universal 13.3.9 and 13.8.13 inputs
remain explicit, together with the later component list, genuine F.9 data,
normalizer bound and noncentrality already required by the comparison.

Source: Aschbacher--Smith, 13.8.14 and 13.8.21(1), pp.951,956--957.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalFitting
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct.ResidualPlacement
variable {G:Type*} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K:Subgroup G} {κ:GroupClass}

theorem comparison_fitting
    (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH:H∈Source.Hz (one L T V₁) T G₁ M)
    (hsource:SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (hex:∀J:Subgroup G,one L T V₁⊔(T:Subgroup G)≤J → J≤G₁ → Group.IsSolvable J → J≤M) :
    fittingPreimageResidual H = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L)≃*alternatingGroup (Fin 6)) ∧
        fittingPreimageResidual H=one L T V₁) ∨ fittingPreimageResidual H=plus L T V₁ := by
  have hr:=whole_residual d hH hsource hex
  have he:fittingPreimageResidual H=Components.Fitting.twoFittingResidual H := by
    unfold fittingPreimageResidual CoveredProduct.ResidualPlacement.residual Components.Fitting.twoFittingResidual
      Components.Fitting.twoFittingResidualIn Components.Fitting.twoFitting
    exact (map_embedded_pResidual 2
      ((fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))) H.subtype).symm
  rw [he]
  rcases hr with hb | ⟨hm,h⟩ | ⟨_,h⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl ⟨hm,h⟩)
  · exact Or.inr (Or.inr h)

theorem covered_comparison
    (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (components:RankReduction.SourceSetup κ H K (one L T V₁) M G₁ T)
    (models:RankReduction.SmallQuotient (K⧸pCore 2 K))
    (hcovered:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms))
    (hNM:normalizer (zero L:Set G)≤M)
    (hsource:SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (hex:∀J:Subgroup G,one L T V₁⊔(T:Subgroup G)≤J → J≤G₁ → Group.IsSolvable J → J≤M)
    (hnoncentral:¬⁅Source.VH H V,H⁆≤Source.UH H V₃) : one L T V₁≤K :=
  Comparison.L₁_le_of_covered d hF9 components models hcovered hNM
    (comparison_fitting d components.local_overgroup hsource hex) hnoncentral

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalFitting
