module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityParabolicAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeAt

/-!
# Source rigidity and splitting at the original G and T

Combine the two dimensional branches under Structural1222At and
Theorem1222ModulesAt. The original universal APIs remain unchanged.
Gaschütz promotes the actual parabolic complement, and the final adapter
discharges rigidity in the existing local-configuration assembly. Its
natural and cyclic producers remain with the parent source assembly.

These are additive specializations of the corresponding rigidity modules;
public results independent of the universal inputs are reused directly.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.804–806
(PDF pp.821–823), with 12.2.2(3) and A.3.12 for containing components.
-/

public noncomputable section

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The exact rigidity-step contract of the original local-configuration
assembly, with both source dimensions and the actual parabolic complement. -/
theorem source_rigidity_step_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  by_cases hd : d = 3
  · exact ThreeRigidity.source_rigidity_step_of_dimension_three_at h D structural A C hnone hTI hd
  · exact HigherRigidity.source_higher_rigidity_step_at h D structural modules A C hnone
      (by have := A.dimension; omega)

/-- The full normalizer, its genuine P-normalizer complement, and its literal
natural tensor action in both dimensions. -/
theorem source_rigidity_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (U : Set G) =
        rigidityHyperplaneResidual L U V ⊔ cyclicPairJoin P U V ⊔ (T : Subgroup G) ∧
      (U.subgroupOf (normalizer (U : Set G))).IsComplement'
        ((normalizer (P : Set G)).subgroupOf (normalizer (U : Set G))) ∧
      Nonempty ((normalizer (U : Set G) ⊓ normalizer (P : Set G) : Subgroup G) ≃*
        (Matrix.SpecialLinearGroup (Fin (d-1)) (ZMod 2) × Equiv.Perm (Fin 3))) ∧
      letI := C.elementary
      ∃ e : Additive U ≃ₗ[ZMod 2] Representation.BinaryDoubledNatural.Space (d-1),
      ∃ f : HigherRigidity.NormalizerQuotient U ≃*
          (Matrix.SpecialLinearGroup (Fin (d-1)) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
        ∀ (g : normalizer (U : Set G)) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom g u)) =
            Representation.BinaryDoubledNatural.tensorRepresentation (d-1)
              (f (HigherRigidity.quotient U g)) (e (Additive.ofMul u)) := by
  rcases (source_rigidity_step_at h D structural modules A C hnone hTI).1 with hd | hd
  · subst d
    obtain ⟨hgen,hcomp,⟨k⟩,e,f,hact⟩ := ThreeRigidity.source_three_normalizer_at h D structural A C hnone hTI
    obtain ⟨s⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    exact ⟨hgen,hcomp,⟨k.trans (MulEquiv.prodCongr s.symm (MulEquiv.refl _))⟩,e,f,hact⟩
  · subst d
    obtain ⟨_,hgen,hcomp,hmodel,e,f,hact⟩ :=
      HigherRigidity.source_higher_normalizer_of_residual_normal_at h D structural A C hnone
        (by decide) (HigherRigidity.source_residual_normal_at h D structural modules A C hnone (by decide))
    refine ⟨hgen,hcomp,hmodel,e,f,?_⟩
    intro g u
    exact hact g u

/-- Gaschütz promotes the actual parabolic complement to the original L. -/
theorem source_rigidity_split_configuration_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    SplitLinearConfiguration L V d := by
  obtain ⟨hd,hself,hcore,hsplit⟩ := source_rigidity_step_at h D structural modules A C hnone hTI
  exact splitLinearConfiguration_of_parabolic_split D hd C.block A.natural hself hcore hsplit

/-- Discharge the rigidity premise of the existing source assembly. Natural
and cyclic producers remain the independent inputs of its original owner. -/
theorem localConfiguration_of_source_analyses_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (naturalStep : NoEscape L V → ChapterI.Section06To08.IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → ChapterI.Section06To08.IsTISubgroup V →
        ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d :=
  localConfiguration_of_source_steps D naturalStep cyclicStep
    (fun _ _ _ _ A C hn ht => source_rigidity_step_at h D structural modules A C hn ht) hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end
