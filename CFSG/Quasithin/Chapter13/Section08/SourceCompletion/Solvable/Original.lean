module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Earlier
public import CFSG.Quasithin.Chapter13.Section02.CoveredNormalizer

/-!
# Solvable exclusion from the original maximal-local hypothesis

The covered natural flag is constructed over the prescribed six-letter
projection. Its L₀ has nontrivial cubic quotient and is normal in LT;
the original Hypothesis12.2.1 therefore supplies its full normalizer bound.
This discharges13.2.2(9) in the complete solvable-overgroup contradiction.

The final consumers retain only the original maximal-local hypothesis,
genuine F.9 applicability, the ambient centralizer/noncentrality assertions
of13.5.4 and universal13.3.9. In particular no normalizer, transvection,
critical-selection, solvable-exclusion or Fitting conclusion is an input.
Source: Aschbacher--Smith,13.2.2(9),13.8.13--15, pp.878,950--952.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.CoveredProduct.ResidualPlacement
open SolvableExclusion
universe u
variable {G:Type u} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (h:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
include d h

theorem covered_normalizer_source
    (hc:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)) :
    normalizer (zero L:Set G)≤M := by
  rcases local_quotient_alternatives d with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨f⟩:=hc
    have hc:=Nat.card_congr (centerCongr (f.symm.trans e)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp),card_bot] at hc
    omega
  · obtain ⟨a⟩:=local_covered_flag_model d e he
    rw [a.zero_normalizer_eq h,←d.local_normalizer]

variable
 (hF9all:∀J∈Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
 (hcentral:centralizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hcomm:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
 (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
include hF9all hcentral hcomm hsource

theorem solvable_overgroup_source
    (H:Subgroup G) (hLT:one L T V₁⊔(T:Subgroup G)≤H) (hHG:H≤G₁)
    (hs:Group.IsSolvable H) : H≤M :=
  solvable_overgroup_of_earlier d hF9all (covered_normalizer_source d h) hcentral hcomm hsource H hLT hHG hs

theorem fitting_center_source (hH:H∈Source.Hz (one L T V₁) T G₁ M) :
    fittingSubgroup (Source.Hstar H) =
      (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype :=
  source_fitting_center d hF9all (covered_normalizer_source d h) hcentral hcomm hsource hH

theorem component_fitting_source (hH:H∈Source.Hz (one L T V₁) T G₁ M)
    (K:Subgroup G) (hK:(K.subgroupOf H).IsCComponent) :
    fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K:Set (Source.Hstar H)) ∧
      IsQuasisimple (Source.starImage H K) :=
  source_component_fitting d hF9all (covered_normalizer_source d h) hcentral hcomm hsource hH K hK

theorem exists_component_source (hH:H∈Source.Hz (one L T V₁) T G₁ M) :
    ∃K:Subgroup G, K≤H ∧ (K.subgroupOf H).IsCComponent ∧
      ¬K≤M ∧ IsQuasisimple (Source.starImage H K) :=
  source_exists_component d hF9all (covered_normalizer_source d h) hcentral hcomm hsource hH

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
