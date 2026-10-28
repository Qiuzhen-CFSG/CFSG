module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.BinaryAutomorphism
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceList
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality

/-!
# Original-source consequences of the covered A₆ comparison

The source maximal-local hypothesis supplies N_G(L₀)=M. The original
13.3.9 and F.9 inputs give the solvable-overgroup and Fitting results, and
the covered comparison proves L₁≤K from the remaining component list.
The actual seed identity then gives U_H=[U_H,K], and the prescribed
H=KL₁T reduction becomes H=KT. In the binary three-dimensional component
case, the earlier 13.8.19 exclusion supplies the full automorphism action.

The component list, its earlier component setup, and 13.8.19 remain explicit
independent inputs. This does not claim the field or small-cover exclusions
needed to produce that list, or completion of the ordinary A₆ branch.
Source: Aschbacher–Smith, 13.8.21(1),(3),(4), printed pp.956–957.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry LinearThree.Geometry.ExternalComponentAction
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The covered source branch of 13.8.21(1),(3),(4), retaining only the
original earlier source inputs and the independently produced list (2).
No normalizer bound, solvable exclusion, Fitting alternative, critical
selection, natural-action marking or seed-generation conclusion is assumed. -/
theorem covered_source_consequences
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hle := SolvableSource.source_covered_comparison c.localSetup c.f9
    (SolvableSource.covered_normalizer_source c.localSetup c.maximal)
    c.centralizer c.noncentral_core c.earlier1339 c.component models hcovered
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal
  refine ⟨hle, ?_, ?_⟩
  · rw [← c.component.generated, sup_eq_left.mpr hle]
  · exact (Section07.ModelExclusions.span_commutator_of_containing_normal_component
      (localNaturalSetup c.localSetup) hKH hn hle).symm

/-- The binary component specialization keeps the original quotient maps:
the returned equivalence is the actual conjugation action on K*. The input
from 13.8.19 excludes H*≅L₃(2), not K*≅L₃(2). -/
theorem covered_source_binary_automorphism
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)
    (hnot : ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL)) :
    Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have models : RankReduction.SmallQuotient (K ⧸ pCore 2 K) :=
    Or.inl ⟨3, le_rfl, by decide, ⟨eK⟩⟩
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let eStar := (Components.componentStarEquiv H K hKH c.component.component).symm.trans eK
  have hH := (covered_source_consequences c models hcovered).2.1
  obtain ⟨e,_⟩ := binary_automorphism_of_supplement H K T hH T.isPGroup' eStar hnot
  exact ⟨e⟩

/-- Actual covered-source assembly after the independent field and cover
exclusions. The quotient list is constructed from the preceding catalogue,
then applied to the literal containment and commutator consumers. This is
still conditional on those exclusions and on the H=KL₁T reduction in c. -/
theorem covered_source_of_exclusions
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple))
    (hmathieu : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22))
    (hcover : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.M22Triple))
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hlist := remainingQuotient_of_exclusions c.catalogue hfield hsix hmathieu hcover
  have hc := covered_source_consequences c
    (RankReduction.smallQuotient_of_source_list hlist) hcovered
  exact ⟨hc.1,hlist,hc.2⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
