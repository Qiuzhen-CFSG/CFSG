module

public import CFSG.Quasithin.Chapter13.Section07.FittingOffenders.Source
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source

/-!
# Selecting the original component after13.7.14

The selected minimal offender centralizes F(H*) but is a nontrivial
two-subgroup and O₂(H*)=1. Generalized-Fitting self-centralization therefore
selects an actual component K* that it moves. Full B.1.5(4) normalizes K*,
and the component commutator dichotomy gives [K*,B*]=K*. Lifting through
the original quotient H→H/O₂(H) constructs a C-component of H with exactly
that image. No component or normalization conclusion is an input.

Source: Aschbacher–Smith, paragraph preceding13.7.15, printed p.943.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual component and its full commutator with the original offender. -/
theorem source_moved_component
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hfaith : Function.Injective σ)
    {B : Subgroup (H ⧸ pCore 2 H)} (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))) :
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (H ⧸ pCore 2 H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      B ≤ normalizer (K.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)) := by
  let U := Section08.Source.UH H V₃
  let : Finite W := Finite.of_surjective (fun x : U => (s.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let : IsElementaryAbelian 2 B := hB.1.1.2
  have hc := source_minimal_offender_centralizes_fitting d h hU hV hne g hs hout σ s hfaith hB hBA
  obtain ⟨J,hJ,hm⟩ := Theory.GroupTheory.exists_component_moved_of_centralizes_fitting 2 B
    (IsElementaryAbelian.isPGroup 2 B) hB.1.1.1 (pCore_quotient_pCore_eq_bot 2) hc
  have hn := ChapterB.source_lemma_B_1_5_4 σ hfaith hB.1 hJ
  have he := Theory.GroupTheory.IsComponent.commutator_eq_self_of_normalizes hJ hn hm
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  obtain ⟨K,hK,hmap⟩ := hJ.isCComponent.exists_map_quotient_eq (pCore 2 H)
  exact ⟨K,hK,hmap.symm ▸ hJ,hmap.symm ▸ hn,hmap.symm ▸ he⟩

/-- Construct the original conjugator, faithful plus action, minimal offender,
and moved C-component, retaining the exact quotient image and seed plane. -/
theorem exists_source_selected_component
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      let U := Section08.Source.UH H V₃
      let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
      let π := QuotientGroup.mk' (pCore 2 H)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ U₀.subgroupOf U)))
          (s : Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (B : Subgroup (H ⧸ pCore 2 H)) (K : Subgroup H),
          Function.Injective σ ∧ IsMinimalBestOffender σ B ∧
          B ≤ (A.subgroupOf H).map π ∧
          B ≤ centralizer (fittingSubgroup (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) ∧
          K.IsCComponent ∧ IsComponent (H ⧸ pCore 2 H) (K.map π) ∧
          B ≤ normalizer (K.map π : Set (H ⧸ pCore 2 H)) ∧
          ⁅K.map π,B⁆ = K.map π ∧
          Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
          subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ := by
  obtain ⟨g,hs,hspan,hout,hE,σ,s,B,hf,hB,hBA,hc,hd,hm⟩ :=
    exists_source_fitting_centralizing_offender d h hU hV hne hk
  let := hE
  obtain ⟨K,hK,hKstar,hn,hcomm⟩ := source_moved_component d h hU hV hne
    (inclusion le_sup_left g) hs hout σ s hf hB hBA
  exact ⟨g,hs,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hc,hK,hKstar,hn,hcomm,hd,hm⟩

end CFSG.Quasithin.Chapter13.Section07
