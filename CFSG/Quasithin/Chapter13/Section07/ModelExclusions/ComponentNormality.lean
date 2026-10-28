module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoveredSeed
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SylowSeedNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness

/-!
# Original component normality and span generation in13.7.5

The actual seed satisfies V₃=[V₃,X] for both printed choices of X.
F.9 gives [U_H,O₂(H)]≤V₁<V₃, so X survives the actual two-core quotient.
The original common Sylow subgroup normalizes X. The source component
normality criterion applies, then conjugate generation gives U_H=[U_H,K].
No component-normality or module-generation conclusion remains a premise.
The genuine earlier F.9 applicability is retained for the Chapter13 owner.

Source: Aschbacher–Smith,13.7.5(1),(2), printed p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem component_normal_of_generating_seed
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (X : Subgroup G) (hXK : X ≤ K)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hseed : ⁅V₃, X⁆ = V₃) : H ≤ normalizer (K : Set G) := by
  have hXH : X ≤ H := hXK.trans hKH
  have hn : ¬ X ≤ Section08.Source.QH H := by
    intro hc
    have hs : V₃ ≤ V₁ := hseed.symm.le.trans
      ((commutator_mono (le_conjugateSpanBy V₃ H) hc).trans hF9.commutator_UH_QH_le_point)
    exact not_le_of_gt hF9.point_lt hs
  have hXi : ¬ X.subgroupOf H ≤ pCore 2 H := by
    intro hc
    apply hn
    intro x hx
    exact mem_map_of_mem H.subtype (hc (show (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H from hx))
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  let S : Sylow 2 H := T.subtype hTH
  have hTS : (S : Subgroup H) ≤
      normalizer (X.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hXH]
    exact subgroupOf_mono H hTX
  have hN := Chapter1.Section02.cComponent_normal_of_sylow_invariant_seed
    (Chapter1.Section02.uniqueness_local_quotient_sqtk d.counterexample.qtke hH.1.1)
    S hK (subgroupOf_mono H hXK) hTS hXi
  exact (normal_subgroupOf_iff_le_normalizer hKH).mp hN

/-- Original13.7.5(1),(2) whenever L₁ is contained in the selected component. -/
theorem component_normal_and_span_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K) :
    H ≤ normalizer (K : Set G) ∧
      ⁅Section08.Source.UH H V₃, K⁆ = Section08.Source.UH H V₃ := by
  have hn := component_normal_of_generating_seed d hH hF9 hKH hK
    (sourceOne L T V₁) hL₁K (T_normalizes_one L T V₁ d.line_stable)
    (seed_commutator_point_residual d)
  exact ⟨hn, span_commutator_of_containing_normal_component d hKH hn hL₁K⟩

/-- Original13.7.5(1),(2) for the covered choice X=L₁,+, even when L₁ is not contained. -/
theorem component_normal_and_span_of_plus_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hplusK : plus L T V₁ ≤ K) :
    H ≤ normalizer (K : Set G) ∧
      ⁅Section08.Source.UH H V₃, K⁆ = Section08.Source.UH H V₃ := by
  have hn := component_normal_of_generating_seed d hH hF9 hKH hK
    (plus L T V₁) hplusK (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable)
    (seed_commutator_plus d hcover)
  exact ⟨hn, span_commutator_of_containing_covered_seed d hcover hKH hn hplusK⟩

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
