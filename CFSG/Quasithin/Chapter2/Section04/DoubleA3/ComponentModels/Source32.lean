module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.LieSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.RefinedRows
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.OddTerminal
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.LinearThreeFourCover
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.Mathieu
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Source
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.MathieuEleven

/-!
# The original source32 component census with its binary Mathieu frontier

Every raw 1.1.5 constructor is consumed with its literal marked action.
The earlier refinement calculations apply only after transporting that
same action through the original component inclusion. Completed model
screens and whole-block absorption leave A₆ or PSL₃(2), or the genuine
binary M₂₂ cover. No arbitrary refined intersection is identified with
one of the retained components.

The final actual consumer applies the completed source33–37 argument to
the retained models. Under the original paired-cubic counterexample
hypotheses it therefore produces a literal ordinary component with
|O₂(K)| = 2 and K/O₂(K) ≃ M₂₂. Exclusion of this binary row remains the
separate final input; it is not hidden in a model or geometry premise.

Source: Aschbacher–Smith 2.4.32–37, printed pp.547–550.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.model_action_source32_or_mathieu
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hm : ModelAction115 K α) :
    (d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
      (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))) ∨
    Nonempty (K ≃* Sporadic.Mathieu.M11) ∨
      (Nat.card (pCore 2 K) = 2 ∧ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) := by
  have h115 := (g.lemma115 hG hM hTM hu).2
  cases hm with
  | lie hs hm hi => exact .inl (g.lie_component_action_source32
      hG hM hTM hu hST hpair K hK α hα ho hs hm hi)
  | two_cover hn hz hm hi =>
      have hm4 := g.two_cover_component_refined hG hM hTM hu hST hpair K hK α hα hi hz hn hm
      exact (g.linear_three_four_cover_from_original hG hM hTM hu hST hpair
        K hK α hα hi hz hm4).elim
  | six σ hs ha => exact (g.six_component_action_false hG h115 K hK α hα σ hs ha).elim
  | seven σ hs ha => exact (g.seven_component_action_false hG h115 K hK α hα σ hs ha).elim
  | odd hm hi =>
      obtain ⟨hL,he⟩ := g.odd_component_action_source32 hG h115 K hK α hα ho hm hi
      exact .inl ⟨hL,.inr he⟩
  | sporadic name hn hm hi =>
      rcases g.sporadic_component_refined hG hM hTM hu hST hpair K hK α hα hi.1 name hn hm
        with hm | ⟨e⟩ | ⟨e⟩ | hm
      · exact .inr (.inl hm)
      · exact (g.mathieu_twentyTwo_component_false hG h115 K hK e.some).elim
      · exact (g.mathieu_twentyThree_component_false hG h115 K hK e.some).elim
      · exact .inr (.inr hm)

theorem SourceCentralizerGeometry.model_action_source32_or_binary_mathieu
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hm : ModelAction115 K α) :
    (d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
      (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))) ∨
      (Nat.card (pCore 2 K) = 2 ∧ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) := by
  rcases g.model_action_source32_or_mathieu hG hM hTM hu hST hpair K hK α hα ho hm with hgood | hbad
  · exact .inl hgood
  · rcases hbad with he | hbinary
    · exact (g.mathieu_eleven_component_false_from_source hG hM hTM hu K hK he.some).elim
    · exact .inr hbinary

/-- The original selected ordinary component retains only the two target
models or the explicitly unresolved Mathieu rows. -/
theorem SourceCentralizerGeometry.original_source32_or_mathieu
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hn : involutionCentralizer g.z₂ ∉ Chapter1.He G) :
    ∃ K : Subgroup (involutionCentralizer g.z₂), IsComponent (involutionCentralizer g.z₂) K ∧
      ((d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
        (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M11) ∨
        (Nat.card (pCore 2 K) = 2 ∧ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22))) := by
  obtain ⟨ho,K,hK,_,_,α,hα,hm⟩ := g.original_component_catalogue hG hM hTM hu hn
  exact ⟨K,hK,g.model_action_source32_or_mathieu hG hM hTM hu hST hpair K hK α hα ho hm⟩

/-- Applying source33–37 to the retained branches and excluding M₁₁
leaves exactly the literal binary M₂₂ component. -/
theorem SourceCentralizerGeometry.binary_mathieu_component_of_source_counterexample
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (e.block.map e.H.subtype) n → False)
    (hfive : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) :
    ∃ K : Subgroup (involutionCentralizer g.z₂), IsComponent (involutionCentralizer g.z₂) K ∧
      Nat.card (pCore 2 K) = 2 ∧ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) := by
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  obtain ⟨K,hK,hm⟩ := g.original_source32_or_mathieu hG hM hTM hu hST hpair hn
  rcases hm with ⟨hL,hm⟩ | hm
  · exact (g.false_of_recognized_component hG hM hTM hu hdelta hcounter hlinear hfive
      hST hpair K hK hL hm).elim
  · rcases hm with ⟨e⟩ | hm
    · exact (g.mathieu_eleven_component_false_from_source hG hM hTM hu K hK e.some).elim
    · exact ⟨K,hK,hm⟩

end CFSG.Quasithin.Chapter2.DoubleA3
