module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Enlargements
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreePositive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Completion

/-!
# The source zero-kernel normalizer reduced to its genuine enlargements

The original action constructs both maximal parabolics. If the full
normalizer of T₁ preserves their two-residuals, their generation gives M.
Otherwise one of the actual parabolics has a strict normal closure inside
its literal enlargement. That enlargement has nontrivial two-core, and
the source subgroup R = T₁ ∩ K is normalized and has index at most two
in the original Sylow intersection. The corrected model list retains Held.

The remaining model-normalizer proof belongs to this same half-Sylow owner;
the conditional applications below do not assert its completion.
Only ModuleChoiceAt is external to that owner, with ultimate discharge by
qt-d-10-nona5-point-control. Source: Aschbacher--Smith 10.2.4--6, pp.747--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The complete original construction before the model normalizer calculation.
Every group in the alternative is the literal subgroup from source 10.2.5. -/
theorem binary_three_normalizer_or_strict_enlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal ∨
    ∃ H I : Subgroup G, Data D H ∧
      (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
      residual H < enlargedResidual T L H ∧
      I ∈ Chapter1.cComponentsIn (enlargement T L H) ∧
      IsQuasisimple (Chapter1.XiQuotient I) ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      SourceLinearThreeReplacement.Overgroups.ClosureModel T I ∧
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (stabilizerIntersection T L H : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ enlargedResidual T L H)
        (enlargedResidual T L H) ∧
      (stabilizerIntersection T L H).relIndex
        ((T : Subgroup G) ⊓ enlargedResidual T L H) ≤ 2 ∧
      (enlargedResidual T L H).pCoreIn 2 ≤ stabilizerIntersection T L H ∧
      (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 ≤
        stabilizerIntersection T L H := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  obtain ⟨H₁,H₂,h₁,h₂,_,hgen⟩ := exists_pair D hmodel hzero hfull ht htn hcross
  by_cases hN₁ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H₁ : Set G)
  · by_cases hN₂ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (residual H₂ : Set G)
    · exact Or.inl (normalizer_le_of_normalizes_pair h₁ h₂ hgen hN₁ hN₂)
    · obtain ⟨hlt,I,hI,hq,hK,hm⟩ := h₂.strict_models hn hN₂
      exact Or.inr ⟨H₂,I,h₂,h₂.enlargement_two_core_ne_bot hn,hlt,hI,hq,hK,hm,
        h₂.normalizer_normalizes_intersection,h₂.enlargedResidual_sylow,
        h₂.intersection_relIndex_le_two hn,h₂.enlargedResidual_core_le_intersection,
        h₂.parabolic_intersection_core_le⟩
  · obtain ⟨hlt,I,hI,hq,hK,hm⟩ := h₁.strict_models hn hN₁
    exact Or.inr ⟨H₁,I,h₁,h₁.enlargement_two_core_ne_bot hn,hlt,hI,hq,hK,hm,
      h₁.normalizer_normalizes_intersection,h₁.enlargedResidual_sylow,
      h₁.intersection_relIndex_le_two hn,h₁.enlargedResidual_core_le_intersection,
      h₁.parabolic_intersection_core_le⟩

/-- Apply the actual parabolic construction to the original normalizer contract.
The residual-normalization calculation remains an explicit local obligation. -/
theorem stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers
    (hchoice : Selection.ModuleChoiceAt T)
    (hparabolic : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
      ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      Selection.BinaryThreeNatural D → sourceMovedFixed D = ⊥ →
      ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
      ∀ H : Subgroup G, Data D H →
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (residual H : Set G)) : StabilizerNormalizerAt T := by
  apply stabilizerNormalizerAt_of_moduleChoice_and_zero_kernel hchoice
  intro L D hmany hmin hfull hn hna hmodel hzero hJ t ht htn hcross
  obtain ⟨H₁,H₂,h₁,h₂,_,hgen⟩ := exists_pair D hmodel hzero hfull ht htn hcross
  exact normalizer_le_of_normalizes_pair h₁ h₂ hgen
    (hparabolic L D hmany hmin hfull hn hna hmodel hzero hJ H₁ h₁)
    (hparabolic L D hmany hmin hfull hn hna hmodel hzero hJ H₂ h₂)

/-- The literal half-join uniqueness consumer, with all containing-pair work
discharged; only the same local residual-normalizer calculation remains. -/
theorem halfSylowUniqueAt_of_moduleChoice_and_parabolic_normalizers
    (hchoice : Selection.ModuleChoiceAt T)
    (hparabolic : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
      ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      Selection.BinaryThreeNatural D → sourceMovedFixed D = ⊥ →
      ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
      ∀ H : Subgroup G, Data D H →
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (residual H : Set G)) : HalfSylowUniqueAt T :=
  halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice
    (stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers hchoice hparabolic)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
