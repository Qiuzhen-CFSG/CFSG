module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalCorePlacement.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Recognition

/-!
# Excluding the original exchanged linear-two component

The elementary structure of U_H and the F.9 commutator bound construct the
literal H/O₂(H) representation on U_H/V₁. Applying the proved module
alternatives and the proved parabolic-core containment to that same action
excludes a nontrivial T-orbit of a PSL₂(2ⁿ) component, for n ≥ 2.

For arbitrary H in Hz, apply this contradiction inside the actual generated
overgroup ⟨K^T⟩L₁T. Relative component membership survives restriction, and
the PSL₂ model transports through K/O₂(K). The Sylow normalizer argument
then proves K normal in H and KL₁T in Hz, the linear-two case of 13.8.16(1).

Only the genuine earlier source hypotheses remain explicit: 12.2.1, F.9
applicability, the centralizer and noncentrality inputs of 13.5.4, and
universal 13.3.9. Their final discharge, and the other component branches,
remain with qt-d-138-components-source. No representation, orthogonal
model, residual identity or parabolic-core placement is an extra input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed pp.952–953 (PDF pp.969–970).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
include d h hF9all hcentral hcomm hsource hH hKH hK

/-- The original exchanged PSL₂ branch is impossible. The elementary
structure, literal quotient action and moving element are all constructed. -/
theorem false_of_source {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) : False := by
  let := d.uh_elementary hH
  have hF9 := hF9all H hH
  have hz : H ≤ normalizer (V₁ : Set G) :=
    hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let ρ := ModuleAlternatives.representation H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  have hρ := ModuleAlternatives.representation_isSourceAction H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  obtain ⟨t, ht, htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  exact false_of_module_alternatives d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn
    (ModuleAlternatives.SourceRecognition.source_module_alternatives
      d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn)

/-- The linear-two case of original 13.8.16(1), on an arbitrary source
H: K is normal in H and the smaller generated overgroup belongs to Hz.
The exclusion is applied inside the actual generated overgroup, with its
PSL₂ identification transported through K/O₂(K). -/
theorem source_normal_and_overgroup {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) :
    (K.subgroupOf H).Normal ∧
      K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) ∈ Source.Hz (one L T V₁) T G₁ M := by
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  have hKJ : K ≤ J := (le_conjugateSpanBy K (T : Subgroup G)).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hLJ : one L T V₁ ≤ J := le_sup_left.trans le_sup_right
  have hJH : J ≤ H := sup_le
    (conjugateSpanBy_le hKH ((le_sup_right.trans hH.1.2).trans H.le_normalizer)) hH.1.2
  have hK' : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hJ : J ∈ Source.Hz (one L T V₁) T G₁ M := by
    have hm := (LocalFitting.source_component d hH hsource
      (SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource)
      K hKH hK).2.1
    have he : (K ⊔ (T : Subgroup G)) ⊔ one L T V₁ = J := by
      apply le_antisymm (sup_le (sup_le hKJ hTJ) hLJ)
      apply sup_le
      · exact conjugateSpanBy_le (le_sup_left.trans le_sup_left)
          ((le_sup_right.trans le_sup_left).trans ((K ⊔ (T : Subgroup G)) ⊔ one L T V₁).le_normalizer)
      · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
    exact he ▸ hm
  have hspan : conjugateSpanBy K (T : Subgroup G) = K := by
    by_contra hmoving
    let e := (componentStarEquiv J K hKJ hK').symm.trans (componentStarEquiv H K hKH hK)
    exact false_of_source d h hF9all hcentral hcomm hsource hJ hKJ hK' hn
      (hmodel.of_mulEquiv e) rfl hmoving
  refine ⟨normal_of_sylow_span_eq H K T hKH (le_sup_right.trans hH.1.2)
    (SolvableSource.source_component_orbit d hF9all
      (SolvableSource.covered_normalizer_source d h) hcentral hcomm hsource hH K hK)
    hspan, ?_⟩
  change conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) ∈ _ at hJ
  rwa [hspan] at hJ

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
