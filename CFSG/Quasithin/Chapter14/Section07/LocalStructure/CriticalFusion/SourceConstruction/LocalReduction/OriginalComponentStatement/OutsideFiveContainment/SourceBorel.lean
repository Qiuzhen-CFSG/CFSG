module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentCentralResidual
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneClosure
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# The actual outside-component Borel normalizes the original I₂

The existing outside-component calculation makes the two-residual of the
actual component Sylow normalizer centralize the original seed V. The
original T normalizes this Borel and covers its two-group residual quotient.
Consequently the whole Borel preserves V₂ and normalizes the literal plane
core closure I₂. This proves the nontrivial cross-normalization clause of
F.1.1 without a module-model or Borel-marking premise.

The source producers currently require the displayed universal earlier
structural and normality inputs. No same-G,T version is asserted here.
Source: Aschbacher–Smith 14.7.40 and 14.7.46, printed pp.1061,1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original Borel lies in the original plane normalizer and normalizes
the actual plane core closure. All Borel and seed data come from the source. -/
theorem local_component_borel_normalizes_plane_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    componentSylowNormalizer T I C ≤ F.Gi 2 ∧
      componentSylowNormalizer T I C ≤ normalizer (planeCoreClosure F : Set G) := by
  let B₀ := componentSylowNormalizer T I C
  obtain ⟨_,_,hBn,_⟩ := local_component_borel_of_not_contains_point
    d h hab structural previous faithful earlier I hI C hC hout
  obtain ⟨hseed,_⟩ := local_component_borel_fixed_actions
    d h hab structural previous faithful earlier I hI C hC hout
  have hBT : B₀ ≤ (pResidual 2 B₀).map B₀.subtype ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T B₀ (le_sup_right.trans hBn)
  have hBG : B₀ ≤ F.Gi 2 := hBT.trans (sup_le
    (hseed.trans ((centralizer_le (F.le_seed 2)).trans (Subgroup.centralizer_le_normalizer _)))
    (F.invariant 2))
  exact ⟨hBG, hBG.trans (le_normalizer_conjugateSpanBy _ _)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
