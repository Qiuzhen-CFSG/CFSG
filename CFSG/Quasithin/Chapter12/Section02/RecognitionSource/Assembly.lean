module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.GlobalTI

/-!
# Conditional assembly of the original 12.2.13 alternatives

The contrary assumption concerns the original chosen V and its original
normalizer N_G(L). Global TI, local split-block construction and terminal
recognition compose to the precise four alternatives of `Theorem12213`.
The natural-row consumer discharges its global-TI input using its actual
quotient action. The universal theorem retains every original quantifier.

The three source implications are explicit, unfinished prerequisites. These
conditional theorems do not claim an unconditional proof of 12.2.13.
Source: Aschbacher--Smith, 12.2.13--27, printed pp.799--807.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Assemble the exact four alternatives on the unchanged choice. The three
inputs are respectively the missing part of 12.2.16, the local analysis
12.2.17--26, and global recognition 12.2.27. -/
theorem alternatives_of_source_steps
    (ti : NoEscape L V → IsTISubgroup V)
    (localStep : NoEscape L V → IsTISubgroup V →
      ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V := by
  classical
  by_cases hn : NoEscape L V
  · obtain ⟨d, C⟩ := localStep hn (ti hn)
    rcases recognize d C hn with hp | ⟨hd, ha⟩ | ⟨hd, hm⟩
    · exact Or.inr (Or.inl ⟨d, C.rank, C.block, hp⟩)
    · subst d
      exact Or.inr (Or.inr (Or.inl ⟨C.block, ha⟩))
    · subst d
      exact Or.inr (Or.inr (Or.inr ⟨C.block, hm⟩))
  · left
    simp only [NoEscape, not_forall] at hn
    obtain ⟨v, hv, hv1, hc⟩ := hn
    exact ⟨v, hv, hv1, hc⟩

/-- The natural row needs no further global-TI premise: its actual action
supplies that source step. Local block construction and ambient recognition
remain explicit earlier proofs. -/
theorem natural_alternatives_of_local_recognition {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) {n : ℕ}
    (natural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) n))
    (localStep : NoEscape L V → IsTISubgroup V →
      ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V :=
  alternatives_of_source_steps
    (fun hn => globalTI_of_natural h D structural hn natural) localStep recognize

/-- Universal assembly, preserving every quantifier of `Theorem12213`.
This is conditional until the three source producers are supplied. -/
theorem theorem12213_of_source_steps (K : GroupClass.{u})
    (ti : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
      Hypothesis1223 K T L → ChosenModule T L V → NoEscape L V → IsTISubgroup V)
    (localStep : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
      Hypothesis1223 K T L → ChosenModule T L V → NoEscape L V → IsTISubgroup V →
        ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ (X : Type u) [Group X] [Finite X]
      (T : Sylow 2 X) (L V : Subgroup X) (d : ℕ),
      Hypothesis1223 K T L → ChosenModule T L V → SplitLinearConfiguration L V d →
        NoEscape L V → RecognizedGroup X d) : Theorem12213 K := by
  intro X _ _ T L V h D
  exact alternatives_of_source_steps (ti X T L V h D) (localStep X T L V h D)
    (fun d => recognize X T L V d h D)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
