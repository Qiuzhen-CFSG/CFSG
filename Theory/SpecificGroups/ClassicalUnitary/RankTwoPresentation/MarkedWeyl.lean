module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.WeylWords
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.AlternatingLength
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices
import Mathlib.Tactic.FinCases

/-!
# Both unitary markings in the original Weyl quotient

The source alternating-word length theorem, with rotation order four,
separates all seven nonidentity presentation words from the source Borel.
The same marked normalizer representatives generate the entire singleton
standard parabolics together with B. The point index is arbitrary in Fin 2,
so both orientations retain the same quotient and full overlap.
Source: DGS, Groups and Graphs, Theorem D, printed p.224; Steinberg,
Lectures on Chevalley Groups, Theorem 4.
-/
@[expose] public noncomputable section
open Subgroup Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (hm : rotationOrder Q=4) (i : Fin 2)

def length : WeylWord → ℕ
  | .one => 0 | .s => 1 | .t => 1 | .st => 2 | .ts => 2
  | .sts => 3 | .tst => 3 | .longest => 4

include hm

theorem source_length (w : WeylWord) :
    Q.tits.wordLength (w.eval (Q.simple (1-i)) (Q.simple i))=length w := by
  have h1 : 1≤rotationOrder Q := by omega
  have h2 : 2≤rotationOrder Q := by omega
  have h3 : 3≤rotationOrder Q := by omega
  have h4 : 4≤rotationOrder Q := by omega
  fin_cases i <;> cases w <;> first
    | exact Q.tits.wordLength_one
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q false h1
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q true h1
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q false h2
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q true h2
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q false h3
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q true h3
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q false h4
    | simpa [WeylWord.eval,length,alternatingWord,mul_assoc] using wordLength_alternatingWord Q true h4

/-- The four-step alternating words are separated in the SAME source Weyl quotient. -/
theorem source_eq_one_iff (w : WeylWord) :
    w.eval (Q.simple (1-i)) (Q.simple i)=1 ↔ w=.one := by
  constructor
  · intro hw
    have hh := source_length Q hm i w
    rw [hw,Q.tits.wordLength_one] at hh
    cases w <;> simp_all [length]
  · rintro rfl; rfl

/-- Both possible endpoint orientations are retained. -/
structure Lifts where
  s : Q.tits.N
  t : Q.tits.N
  s_class : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s=Q.simple (1-i)
  t_class : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) t=Q.simple i

namespace Lifts
variable (d : Lifts Q i)

theorem eval_mem_borel_iff (w : WeylWord) :
    w.eval (d.s : X ⧸ Q.D) (d.t : X ⧸ Q.D)∈Q.tits.B ↔ w=.one := by
  constructor
  · intro hb
    have hq : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
        (w.eval d.s d.t)=1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_,(w.eval d.s d.t).property⟩
      change Q.tits.N.subtype (w.eval d.s d.t)∈Q.tits.B
      rw [WeylWord.map_eval]
      exact hb
    rw [WeylWord.map_eval,d.s_class,d.t_class] at hq
    exact (source_eq_one_iff Q hm i w).mp hq
  · rintro rfl
    exact Q.tits.B.one_mem

omit hm in
theorem simple_parabolic (j : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n=Q.simple j) :
    Q.tits.standardParabolic {Q.simple j}=Q.tits.B ⊔ closure {(n : X ⧸ Q.D)} := by
  apply le_antisymm
  · intro g hg
    have hh : g∈(Q.tits.B : Set (X ⧸ Q.D)) ∪ Q.tits.bruhatCell (Q.simple j) := by
      rwa [←singleton_parabolic_cells (Q.simple_mem j)]
    rcases hh with hb|hc
    · exact Subgroup.mem_sup_left hb
    · rw [Theory.AlgebraicGroup.TitsSystem.bruhatCell,
        Theory.AlgebraicGroup.TitsSystem.B_mul_representativeSet_mul_B Q.tits.B Q.tits.N _ n hn] at hc
      obtain ⟨a,ha,b,hb,he⟩ := DoubleCoset.mem_doubleCoset.mp hc
      rw [he]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (subset_closure (Set.mem_singleton _)))) (Subgroup.mem_sup_left hb)
  · apply sup_le (Q.tits.B_le_standardParabolic _)
    apply (Subgroup.closure_le _).2
    rintro x rfl
    exact Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n hn)
end Lifts
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl
