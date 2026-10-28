module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ContainingModels
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateStructure
/-!
# The exceptional seed lift with only the J₄ alternative remaining

The actual normalized seed supplies one of the three exceptional simple
sections. The known-simple containing catalogue proves that its unique
normal component either inherits the same candidate or has J₄ two-core
quotient. Equality preserves the original linear diagram action; enlarged
J₂ or M₂₃ quotients are already terminal candidates. No full A.3.12 input
is used. This is a reduction with a genuine remaining J₄ source obligation.
Source: Aschbacher–Smith 13.6.27, p.934, and A.3.12, pp.47–48.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Lift the actual exceptional candidate, retaining the single unresolved
J₄ containing row with its literal normal component. -/
theorem normal_candidate_or_jankoFour
    (hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (S : Sylow 2 H) {B : Subgroup H} (hB : B ∈ Chapter1.L H S)
    (hn : (S : Subgroup H) ≤ normalizer (B : Set H)) (hc : Candidate (S : Subgroup H) B) :
    ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧ B ≤ K ∧
      (Candidate (S : Subgroup H) K ∨ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) := by
  have hm : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel (B ⧸ pCore 2 B) := by
    rcases hc with hJ | hM | ⟨e, _⟩
    · exact Or.inl hJ
    · exact Or.inr (Or.inl hM)
    · exact Or.inr (Or.inr ⟨e⟩)
  obtain ⟨K, hK, hKn, hBK, he | hJ | hM | hJ4⟩ :=
    ChapterA.Section03.SourceEmbeddings.Exceptional.exists_normal_containing_models hQ S hB hn hm
  · exact ⟨K, hK, hKn, hBK, Or.inl (he ▸ hc)⟩
  · exact ⟨K, hK, hKn, hBK, Or.inl (Or.inl hJ)⟩
  · exact ⟨K, hK, hKn, hBK, Or.inl (Or.inr (Or.inl hM))⟩
  · exact ⟨K, hK, hKn, hBK, Or.inr hJ4⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
