module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Paired
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Original
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Small
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalAdequate
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalOddTwo

/-!
# Binary component models above the original generation minimum

The original 11.3.2 counterexample gives n(H) ≥ n > 1. The genuine
E.2.2 catalogue and its numerical generation bounds therefore exclude
all normal odd-characteristic rows, the binary derived symplectic row,
and paired prime-field PSL₂ at primes at least seven. The exceptional
PSL₂(5) row is carried through the concrete PSL₂(4) equivalence.

For a normal component, the remaining models are on its literal image
in H/core_H(M). For a paired component, the established core identity
identifies that image with K/O₂(K). Every surviving field exponent is
at least n(H); no equality across the solvable kernel is asserted.
The final consumer applies the normal sieve to the original ComponentSeed.
Recognition/Models combines both branches with the faithful overcomponent.

This is the numerical sieve in 11.3.5(1), not its rank-one conclusion:
the A.3.12 and FF-module exclusions and the reverse parameter inequality
remain with the parameter-component owner. The linear-geometry owner
retains final discharge of the genuine preceding 11.0–11.2 source inputs.
Source: Aschbacher--Smith, E.2.2, pp.215–216, and 11.3.5, pp.771–772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The actual exchanged component has a binary PSL₂ or Suzuki quotient.
Odd prime fields above five contradict the original generation lower bound. -/
theorem ComponentSeed.paired_binary_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal) :
    (∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  rcases s.paired_models h pr hc hs hn with hm | hm | ⟨r,hr,ho,hm⟩
  · exact Or.inl hm
  · exact Or.inr hm
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  have hsolv := counterexample_not_solvable h pr hc hs
  have hgen := ComponentSeed.intrinsic_supplement s h.outside.1.1.2
  have hcore : ChapterB.minimalParabolicCore P hP = pCore 2 H :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
      (s.paired_radical_eq_twoCore h pr hc hs hn)
  let e := ComponentSeed.quotientImageEquivOfCore s (ChapterB.minimalParabolicCore P hP) hcore
  let := s.quasisimple
  rcases Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.prime_model_binary_or_ge_seven
      hr ho hm with hfour | hlarge
  · exact Or.inl ⟨2,by decide,ChapterE.Structure.NumericalBounds.paired_bender_upper
      ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv J
      s.component.2 hgen hn (.inl ⟨by decide,hfour.of_mulEquiv e.symm⟩),hfour⟩
  · let : Fact r.Prime := ⟨hr⟩
    have hu := ChapterE.Structure.NumericalBounds.paired_prime_upper_one
      ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv J
      s.component.2 hgen hn hlarge (hm.of_mulEquiv e.symm)
    have hl := degree_le_parameter h pr hc hs
    have hnon := S.nonbinary
    omega

namespace Models
open ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {X : Type u} [Group X] [Finite X] {κ : GroupClass.{u}}

/-- Prune the normal source catalogue at n(H)>1, retaining the literal
maximal-core quotient and each actual binary field exponent. -/
theorem normal_binary_star_models
    (hA : ChapterA.Section02.TheoremA κ X)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y], ChapterA.Section02.TheoremC κ Y)
    (hX : IsSQTK κ X) (P : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (hsolv : ¬ Group.IsSolvable X) (hn : 1 < generationParameter X)
    (J : Subgroup X) (hJ : J.IsCComponent) [J.Normal]
    (hgen : J ⊔ (P : Subgroup X) = ⊤) :
    let I := sourceImage (ChapterB.minimalParabolicMax P hP) J
    ∃ f : ℕ, 2 ≤ f ∧ generationParameter X ≤ f ∧
      (ClassicalGroup.IsPSL I 2 (2 ^ f) ∨ ClassicalGroup.IsPSU I 3 (2 ^ f) ∨
        ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f) ∨
        ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
          Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  let I := sourceImage (ChapterB.minimalParabolicMax P hP) J
  rcases source_normal_geometric_cases hA hC hX P hP hsolv J hJ hgen with
    h2 | h3 | hb | hl | hsp | hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hX P hP hsolv J hJ hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hX P hP hsolv J hJ hgen hp ho
        (.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hX P hP hsolv J hJ hgen hp ho
        (.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      exact ⟨f,hf,normal_classical_parameter_le hA hX P hP hsolv J hJ
        hgen (.inl ⟨hf,hm⟩),.inl hm⟩
    | unitary f hf hm =>
      exact ⟨f,hf,normal_classical_parameter_le hA hX P hP hsolv J hJ
        hgen (.inr (.inl ⟨hf,hm⟩)),.inr (.inl hm)⟩
    | suzuki m hm he =>
      exact ⟨2*m+1,by omega,(normal_suzuki_generation P hP hsolv J hJ hgen hm he).2,
        .inr (.inr (.inr (.inr ⟨m,by omega,rfl,he⟩)))⟩
  · obtain ⟨f,hf,hm⟩ := hl
    have hu := normal_classical_parameter_le hA hX P hP hsolv J hJ
      hgen (.inr (.inr ⟨hf,hm⟩))
    exact ⟨f,by omega,hu,.inr (.inr (.inl hm))⟩
  · obtain ⟨f,hf,hm⟩ := hsp
    exact ⟨f,hf,normal_symplectic_parameter_le hA hX P hP hsolv J hJ
      hgen (by omega) hm,.inr (.inr (.inr (.inl hm)))⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le P hP hsolv J hJ hgen hbi)).elim
end Models

open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels in
/-- Apply the normal numerical sieve to the component selected from the
original counterexample. The image remains in H/core_H(M), with the
literal prescribed Sylow and unique maximal subgroup. -/
theorem ComponentSeed.normal_binary_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let I := sourceImage (ChapterB.minimalParabolicMax P hP) (K.subgroupOf H)
    ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      (ClassicalGroup.IsPSL I 2 (2 ^ f) ∨ ClassicalGroup.IsPSU I 3 (2 ^ f) ∨
        ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f) ∨
        ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
          Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  let := hn
  have hl := degree_le_parameter h pr hc hs
  have hnon := S.nonbinary
  exact Models.normal_binary_star_models ChapterA.Section02.theoremA_knownSimple
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) (outside_sqtk h)
    (T.subtype h.outside.1.1.2)
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))
    (counterexample_not_solvable h pr hc hs) (by omega) (K.subgroupOf H) s.component.2
    (s.intrinsic_supplement h.outside.1.1.2)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
