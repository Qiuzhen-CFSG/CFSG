module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Numerical
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Normal

/-!
# The generation bound from a literal binary PSL₂ component

Retain the actual quotient K/O₂(K) and its independently marked field
exponent f. For a normal component, its image in H/O₂(H) is simple and
is F*(H/O₂(H)); the existing PSL₂ value supplies E-generation at f.
Lifting through the original two-core gives n(H) ≤ f. For a paired
component, the previously proved maximal-core identity and Bender
upper bound give the same inequality.

The field-four consumer in Models/Small combines this bound with the
original n(H) ≥ n > 1 to prove equality and the outside-component
conclusion in that row. No general lower bound for n(H) is inferred
from a quotient value. The parameter-component owner retains the
larger-field recognition and equality arguments.
Source: Aschbacher--Smith E.1.11--14, E.2.2, and 11.3.5, pp.212--216,771.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- A concrete PSL₂(2^f) model of the original component bounds the actual
generation minimum, whether or not the component is normal in H. -/
theorem ComponentSeed.linear_parameter_le (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    ChapterE.generationParameter H ≤ f := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hgen := s.intrinsic_supplement h.outside.1.1.2
  by_cases hn : J.Normal
  · let := hn
    let := s.quasisimple
    let e := s.intrinsicQuotientEquiv
    have hmJ := hm.of_mulEquiv e.symm
    let : IsQuasisimple (J ⧸ pCore 2 J) := IsQuasisimple.of_mulEquiv e
    have hsimple : IsSimpleGroup (J ⧸ pCore 2 J) := by
      obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hmJ
      have hcard4 : 4 ≤ Nat.card F := by
        rw [hcard]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
      let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
      exact a.isSimpleGroup
    let := hsimple
    obtain ⟨hsF,⟨a⟩,hFS⟩ :=
      Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.normal_component_quotient_structure
        P J s.component.2 hgen
    let := hsF
    have he := ChapterE.ValuesEvenClassical.generationParameter_eq_of_isPSL2
      (Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.sqtk_quotient_of_two_kernel
        (outside_sqtk h) (pCore 2 H) pCore_isPGroup)
      hf (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) hFS
      (hmJ.of_mulEquiv a)
    apply ChapterE.generationParameter_le (by omega)
    apply ChapterE.IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
    have hh := ChapterE.isEGenerated_generationParameter_of_pos (G := H ⧸ pCore 2 H)
      (by rw [he]; omega)
    rwa [he] at hh
  · have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    have hsolv := counterexample_not_solvable h pr hc hs
    have hcore : ChapterB.minimalParabolicCore P hP = pCore 2 H :=
      (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
        (s.paired_radical_eq_twoCore h pr hc hs hn)
    let e := s.quotientImageEquivOfCore (ChapterB.minimalParabolicCore P hP) hcore
    exact ChapterE.Structure.NumericalBounds.paired_bender_upper
      ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv J
      s.component.2 hgen hn (.inl ⟨hf,hm.of_mulEquiv e.symm⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
