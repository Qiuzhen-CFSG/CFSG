module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Structure
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Original
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The three paired models on the original component quotient

The genuine E.2.2 catalogue applies to the simple image in H/J. In the
paired case J = O₂(H), so the original inclusion identifies that image
with K/O₂(K). Transport the concrete PSL₂ and Suzuki equivalences through
this identification. The checked generation witnesses also give n(H) ≤ f
for each binary model at its own field exponent f.

The exponent is not relabelled as n(H): equality and exclusion of the
Suzuki and odd-prime rows remain part of the 11.3.5 recognition argument.
Source: Aschbacher--Smith, E.2.2 and 11.3.5(1), pp.215--216,771.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

theorem ComponentSeed.paired_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal) :
    (∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
    (∃ r : ℕ, r.Prime ∧ Odd r ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 r) := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h p hc)
  have hsolv := counterexample_not_solvable h p hc hs
  have hgen := ComponentSeed.intrinsic_supplement s h.outside.1.1.2
  have hcore : ChapterB.minimalParabolicCore P hP = pCore 2 H :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
      (s.paired_radical_eq_twoCore h p hc hs hn)
  let e := ComponentSeed.quotientImageEquivOfCore s (ChapterB.minimalParabolicCore P hP) hcore
  have hm := ChapterE.Structure.source_original_paired_models
    ChapterA.Section02.theoremA_knownSimple
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    (outside_sqtk h) P hP hsolv J s.component.2 hgen hn
  rcases hm with ⟨f,hf,hm⟩ | ⟨m,hm,⟨eM⟩⟩ | ⟨r,hr,ho,hm⟩
  · exact Or.inl ⟨f,hf,ChapterE.Structure.NumericalBounds.paired_bender_upper
      ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv J
      s.component.2 hgen hn (.inl ⟨hf,hm⟩),hm.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨m,hm,ChapterE.Structure.NumericalBounds.paired_bender_upper
      ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv J
      s.component.2 hgen hn (.inr ⟨m,by omega,rfl,⟨eM⟩⟩),⟨e.trans eM⟩⟩)
  · exact Or.inr (Or.inr ⟨r,hr,ho,hm.of_mulEquiv e⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
