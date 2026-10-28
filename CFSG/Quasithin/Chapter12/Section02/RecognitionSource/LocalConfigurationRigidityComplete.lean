module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherNoncentral
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeNormalizerTensor
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationAssembly

/-!
# Source rigidity and splitting for original 12.2.25–26

The higher branch now proves residual normality using the exhaustive binary,
marked A₇ and noncentral-Fitting reductions. Combine it with the checked
transfer branch in dimension three. This proves the original dimension
cutoff, self-normalization of L, O₂(L)=V and a genuine complement to V in
the literal N_L(U), preserving T and its containment in L.

The remaining source exports retain the original cubic actor P, the ambient
centralizers, the order-two Sylow center, N_G(U)=YIT, its actual complement
N_G(U)∩N_G(P), and the conjugation equations for the natural tensor action.
The parabolic complement feeds the existing Gaschütz theorem. Finally the
existing local-configuration assembly is applied with its rigidity premise
fully discharged. Only the authorized earlier Structural1222 and universal
seven-module theorems, and the independent natural and cyclic analyses,
remain inputs; their producers belong to the parent local-configuration task.

Source: Aschbacher–Smith, original 12.2.25–26, printed pp.804–806
(PDF pp.821–823), with 12.2.2(3) and A.3.12 for the containing components.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The exact rigidity-step contract of the original local-configuration
assembly, with both source dimensions and the actual parabolic complement. -/
theorem source_rigidity_step
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  by_cases hd : d = 3
  · exact ThreeRigidity.source_rigidity_step_of_dimension_three h D structural A C hnone hTI hd
  · exact HigherRigidity.source_higher_rigidity_step h D structural modules A C hnone
      (by have := A.dimension; omega)

/-- The cubic pair actor, with its original subgroup P. -/
theorem source_rigidity_prime_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : Nat.card P = 3 := by
  by_cases hd : d = 3
  · subst d
    exact ThreeRigidity.source_prime_card_three h D structural A C hnone
  · have hd' : 3 < d := by have := A.dimension; omega
    exact HigherRigidity.cubic_of_residual_normal h D structural A C hnone hd'
      (HigherRigidity.source_residual_normal h D structural modules A C hnone hd')

/-- Vanishing of the original central Sylow factor, used for the ambient
centralizers and the center clause of 12.2.25. -/
theorem source_rigidity_component_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  by_cases hd : d = 3
  · subst d
    have he := (ThreeRigidity.source_transfer_conclusions h D structural A C hnone hTI).2.1
    have hh := B.common_trivial
    rw [←he,inf_idem] at hh
    exact hh
  · have hd' : 3 < d := by have := A.dimension; omega
    exact higher_component_centralizer_eq_bot_of_residual_normal h D A C B
      (HigherRigidity.source_residual_normal h D structural modules A C hnone hd')
      (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)

/-- Ambient self-centralization, including the literal U=C_G(U) clause. -/
theorem source_rigidity_selfCentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    centralizer (V : Set G) = V ∧ centralizer (U : Set G) = U :=
  higher_selfCentralizing_of_kernel_vanishing h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone)
    (source_rigidity_component_centralizer h D structural modules A C hnone hTI)

/-- The original Sylow center has order two, not just its quotient image. -/
theorem source_rigidity_sylow_center_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    Nat.card (center T) = 2 := by
  have hCV := (source_rigidity_selfCentralizing h D structural modules A C hnone hTI).1
  let Z := (center T).map (T : Subgroup G).subtype
  have hZC : Z ≤ centralizer (T : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ t ht
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t,ht⟩)
  have hZV : Z ≤ V := by
    rw [←hCV]
    exact hZC.trans (centralizer_le D.le_sylow)
  have hbound : Nat.card (center T) ≤ 2 := by
    have hc : Nat.card Z = Nat.card (center T) := card_map_of_injective (T : Subgroup G).subtype_injective
    rw [←hc]
    exact (card_le_of_le (le_inf hZV hZC)).trans (RigidityKernel.chosen_sylow_fixed_card D A)
  let : Nontrivial V := (nontrivial_iff_ne_bot V).mpr D.ne_bot
  let : Nontrivial T := (inclusion_injective D.le_sylow).nontrivial
  let : Nontrivial (center T) := T.isPGroup'.center_nontrivial
  have hlo : 1 < Nat.card (center T) := Finite.one_lt_card
  omega

/-- The full normalizer, its genuine P-normalizer complement, and its literal
natural tensor action in both dimensions. -/
theorem source_rigidity_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
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
  rcases (source_rigidity_step h D structural modules A C hnone hTI).1 with hd | hd
  · subst d
    obtain ⟨hgen,hcomp,⟨k⟩,e,f,hact⟩ := ThreeRigidity.source_three_normalizer h D structural A C hnone hTI
    obtain ⟨s⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    exact ⟨hgen,hcomp,⟨k.trans (MulEquiv.prodCongr s.symm (MulEquiv.refl _))⟩,e,f,hact⟩
  · subst d
    obtain ⟨_,hgen,hcomp,hmodel,e,f,hact⟩ :=
      HigherRigidity.source_higher_normalizer_of_residual_normal h D structural A C hnone
        (by decide) (HigherRigidity.source_residual_normal h D structural modules A C hnone (by decide))
    refine ⟨hgen,hcomp,hmodel,e,f,?_⟩
    intro g u
    exact hact g u

/-- Gaschütz promotes the actual parabolic complement to the original L. -/
theorem source_rigidity_split_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    SplitLinearConfiguration L V d := by
  obtain ⟨hd,hself,hcore,hsplit⟩ := source_rigidity_step h D structural modules A C hnone hTI
  exact splitLinearConfiguration_of_parabolic_split D hd C.block A.natural hself hcore hsplit

/-- Discharge the rigidity premise of the existing source assembly. Natural
and cyclic producers remain the independent inputs of its original owner. -/
theorem localConfiguration_of_source_analyses
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (naturalStep : NoEscape L V → ChapterI.Section06To08.IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → ChapterI.Section06To08.IsTISubgroup V →
        ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d :=
  localConfiguration_of_source_steps D naturalStep cyclicStep
    (fun _ _ _ _ A C hn ht => source_rigidity_step h D structural modules A C hn ht) hnone hTI
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource