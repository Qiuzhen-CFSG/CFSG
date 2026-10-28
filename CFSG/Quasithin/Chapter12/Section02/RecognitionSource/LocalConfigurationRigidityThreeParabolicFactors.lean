module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeOddCore

/-!
# Canonical dimension-three parabolic factors

The proved four-group and odd-core calculations give residual-image
normality, eliminate the common central factor, and give |P|=3.
The existing relative pair-normality theorem then feeds the canonical
factor construction: K=C_{N_L(U)}(P), N_L(U)=UVK, separation of UV and K,
and a K-invariant complement to U∩V inside U.

This module exports the complete factor record from the original source
inputs and applies both the literal parabolic complement and Gaschütz
consumers. Higher-dimensional assembly stays with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25--26, printed p.806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

/-- The canonical parabolic factors, with the original fixed actor and
invariant complement, from the original dimension-three source inputs. -/
theorem source_rigidity_factors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧ ParabolicFactorization L V U P := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let := source_oddCore_elementary h D structural A C hnone
  have hn := residual_image_normal_of_abelian_oddCore D A C B
    (((structural G T L h).2.2 V D).1) hTI inferInstance
  have hz := kernel_vanishing_of_residual_image_normal h D structural A C B hn
  have hs := higher_kernel_vanishing_consequences D B hz
  exact ⟨higher_normalizer_eq_of_kernel_vanishing h D structural A C B hz,
    RigidityResidual.component_core_of_centralizers D B,
    RigidityParabolic.factorization_of_cubic_and_pair_normalized D A C
      (source_prime_card_three h D structural A C hnone) (C.core_le_sylow.trans hs.1)
      (parabolic_normalizes_pair_of_residual_image_normal h D structural A C B hn)⟩

/-- The canonical factors feed the existing literal complement and Gaschütz
consumers; no complement or tensor-recognition premise is retained. -/
theorem source_parabolic_and_split_from_factors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    ParabolicSplitting T L V U ∧ SplitLinearConfiguration L V 3 := by
  obtain ⟨hM,hcore,F⟩ := source_rigidity_factors h D structural A C hnone hTI
  exact ⟨parabolicSplitting_of_cyclic_factorization D C hM F,
    splitLinearConfiguration_of_cyclic_factorization D A C (Or.inl rfl) hM hcore F⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
