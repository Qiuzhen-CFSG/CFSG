module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Derived
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups.OriginalSource

/-!
# Applying the proved field reductions to unrestricted original overgroups

The published original context supplies component normality, the model
catalogue and the residual input. Reducing to KL₁T preserves the component
and its intrinsic two-core quotient. Thus the derived-family exclusions
and signed parameter bounds apply to every component of the original H.
The full higher-field and whole-quotient binary exclusions remain with
qt-d-138-fields-source; the original preceding inputs retain their producers
through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20–21, printed pp.954–957.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Chapter1.Section02.LocalModels Components.Models
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
include d h hF9 hcentral hcomm hH hKH hK

/-- Neither higher-field derived family can occur in any original component;
no assumption H=KL₁T is imposed on this application. -/
theorem original_no_higher_derived (n : ℕ) (hn : 1 < n) :
    ¬ (IsSp4DerivedAt (K ⧸ pCore 2 K) (2^n) ∨
      IsG2DerivedAt (K ⧸ pCore 2 K) (2^n)) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_no_higher_derived (Overgroups.reducedContext c K hKH hK) n hn

/-- The current signed field sieve on the original component quotient,
including the ordinary and covered local cases and every surviving parity. -/
theorem original_higher_field_parameter_list
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∨
        ∃ unitary : Bool,
          (IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
            IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) ∧
          ((unitary = false ∧ (Odd n ∨ n = 2)) ∨
            (unitary = true ∧ (Even n ∨ n = 3)))) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_higher_field_parameter_list (Overgroups.reducedContext c K hKH hK) hfield

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
