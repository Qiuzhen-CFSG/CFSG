module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.CentralQuotientSource
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.KnownSimple

/-!
# A₅ preparation on the original chosen module

The natural central quotient reconstructs the full chosen module by
projectivity. Homogeneity and the Sylow two-group then supply the invariant
flag. On that same flag the common-normal and conjugate-action arguments
establish F.9.1 for every actual member of H_z. The nonabelian recognition
and F.9 closure equivalence also put V in O₂(H) in the A₅ counterexample.

Only the earlier natural central-quotient classification is retained. No
marked Context, F.9 applicability or abelian-closure conclusion is assumed.
Source: Aschbacher–Smith 13.3.2(3), 13.5.7–12 and 13.6.2, pp.885,917–926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.Preparation
open Section06.TerminalContradiction.Ratio Section05.A5Source
open Section06.SourceAbelian
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the original A₅ flag and the universal 13.5.7 application on it. -/
theorem five_preparation_of_central_quotient
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v)) :
    ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      ∃ _d : Context T L V V₁ V₂ V₃,
        let := D.elementary
        Earlier1357 T L V V₃ V₁ (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
  obtain ⟨V₁,V₂,V₃,h23,⟨d⟩⟩ :=
    Section03.A5Setup.exists_context_of_natural_central_quotient h D e a ha
  let := D.elementary
  exact ⟨V₁,V₂,V₃,h23,d,earlier1357_knownSimple d⟩

/-- The same original choice supplies the abelian local closures and actual
O₂(H) containment required by the terminal A₅ source consumer. -/
theorem five_abelian_family_of_central_quotient
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v))
    (hcounter : Section06.CentralizerReduction.IsA5Counterexample G) :
    ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      ∃ _d : Context T L V V₁ V₂ V₃,
        let := D.elementary
        Earlier1357 T L V V₃ V₁ (centralizer (V₁ : Set G)) (normalizer (L : Set G)) ∧
        ∀ H ∈ Section08.Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
            (centralizer (V₁ : Set G)) (normalizer (L : Set G)),
          IsMulCommutative (conjugateSpanBy V H) ∧ V ≤ H.pCoreIn 2 := by
  obtain ⟨V₁,V₂,V₃,h23,d,hF⟩ := five_preparation_of_central_quotient h D e a ha
  let := D.elementary
  refine ⟨V₁,V₂,V₃,h23,d,hF,?_⟩
  intro H hH
  have hU : IsMulCommutative (conjugateSpanBy V₃ H) := by
    by_contra hn
    have hm := source_nonabelian_classification_knownSimple d hH hn
    rcases hm with hu | hl
    · exact hcounter.1 hu
    · exact hcounter.2 hl
  have he := (source13_5_10_knownSimple d hH).1
  exact ⟨he.1.mp hU,he.2.mp hU⟩

end CFSG.Quasithin.Chapter13.Section05.Preparation
