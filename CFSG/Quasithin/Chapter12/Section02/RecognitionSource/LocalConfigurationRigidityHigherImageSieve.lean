module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherCentralCovers
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSevenFixer
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherNormalizerTensor

/-!
# Applying the containing-image exclusions to higher local rigidity

The ordinary binary, central-cover, SL₂(7), small alternating, A₇ and
natural seven-plane alternatives now all feed the original residual-normality
and parabolic-splitting consumer. The actual component chain also excludes
its literal A₇ image without any catalogue premise.

This is a conditional reduction: constructing the exhaustive image list from
12.2.2 and A.3.12 remains with qt-d-12213-local-rigidity, as do its discharge
and final assembly with dimension three. No source classification is asserted
by the displayed disjunction alone.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.805–806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- All ordinary central-cover rows and the literal exceptional A₇ and seven-plane
rows are discharged at the original residual-normality and rigidity consumer.
Establishing this containing-image list from 12.2.2 and A.3.12 remains separate. -/
theorem source_rigidity_of_containing_image_list
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hmodel :
      (∃ m, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) ∨
      (∃ m, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL
        ((ThreeRigidity.image T U K) ⧸ center (ThreeRigidity.image T U K)) m 2) ∨
      Chapter1.Section02.LocalModels.IsSL (ThreeRigidity.image T U K) 2 7 ∨
      (Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 5 ∨
        Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 6 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover (ThreeRigidity.image T U K) 6) ∨
      Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∨
      ∃ N : Subgroup (ThreeRigidity.image T U K), ∃ _ : N.Normal,
        Chapter1.Section02.LocalModels.NaturalSL2Action (ThreeRigidity.image T U K) N 7) :
    normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have he : rigidityHyperplaneResidual L U V = K := by
    rcases hmodel with ⟨m,hm,hmodel⟩ | ⟨m,hm,hmodel⟩ | hmodel | hmodel | hmodel | ⟨N,hN,hmodel⟩
    · exact residual_eq_containing_of_binary_linear_image h D structural A C B hd hKN hK hYK hm hmodel
    · exact residual_eq_containing_of_binary_central_quotient h D structural A C B hd hKN hK hYK hm hmodel
    · exact residual_eq_containing_of_special_linear_seven h D structural A C B hd hKN hK hYK hmodel
    · exact residual_eq_containing_of_small_alternating_image h D structural A C B hd hKN hK hYK hmodel
    · exact (no_alternating_seven_containing_image h D structural A C B hd hKN hYK hn hmodel).elim
    · exact (sectionRadical_quotient_no_natural_seven_plane h D structural A C hnone
        (ThreeRigidity.image T U K) N hmodel).elim
  have hnormal : normalizer (sectionRadical T U : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G) := by simpa only [he] using hn
  exact ⟨hnormal,source_rigidity_step_of_residual_normal h D structural A C hnone hd hnormal⟩

/-- The actual normal containing component cannot have the literal exceptional
A₇ image, regardless of whether it equals the original residual. -/
theorem source_containing_component_without_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀⟩ :=
    source_containing_component_chain h D structural A C hnone hd
  exact ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,
    no_alternating_seven_containing_image h D structural A C
      (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hYK hn⟩

/-- The same concrete image alternatives supply the full normalizer, its actual
complement, and the literal tensor-action marking, with no further local premise. -/
theorem source_higher_normalizer_of_containing_image_list
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hmodel :
      (∃ m, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) ∨
      (∃ m, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL
        ((ThreeRigidity.image T U K) ⧸ center (ThreeRigidity.image T U K)) m 2) ∨
      Chapter1.Section02.LocalModels.IsSL (ThreeRigidity.image T U K) 2 7 ∨
      (Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 5 ∨
        Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 6 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover (ThreeRigidity.image T U K) 6) ∨
      Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∨
      ∃ N : Subgroup (ThreeRigidity.image T U K), ∃ _ : N.Normal,
        Chapter1.Section02.LocalModels.NaturalSL2Action (ThreeRigidity.image T U K) N 7) :
    d = 4 ∧
      normalizer (U : Set G) =
        rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ⊔ (T : Subgroup G) ∧
      (U.subgroupOf (normalizer (U : Set G))).IsComplement'
        ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
      Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3))) ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] TensorModel.Space,
      ∃ f : NormalizerQuotient U ≃* TensorModel.Factors,
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            TensorModel.tensor (f (quotient U g)) (e (Additive.ofMul u)) := by
  exact source_higher_normalizer_of_residual_normal h D structural A C hnone hd
    (source_rigidity_of_containing_image_list h D structural A C hnone hd
      hKN hK hYK hn hmodel).1

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
