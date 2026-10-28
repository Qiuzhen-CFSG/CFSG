module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Kernel
public import CFSG.Quasithin.ChapterA.Section02.Alternating
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore

/-!
# Case split for the simultaneous A/B/C induction

The simultaneous induction has only two ambient cases. A simple ambient group
cannot fail Theorem A because its counterexample reduction proves nonsimplicity;
a nonsimple minimal counterexample therefore supplies an actual Theorem-A
counterexample. These are logical source reductions, not classification
assumptions.

Source: Aschbacher–Smith A.2.13, printed p.38.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]

theorem not_theoremA_iff : ¬ TheoremA K G ↔
    ∃ (S : Type u) (_ : Group S) (_ : Finite S) (p : ℕ),
      CounterexampleToTheoremA K G S p := by
  classical
  simp only [TheoremA, not_forall, CounterexampleToTheoremA]
  constructor
  · rintro ⟨hq, hk, S, hS, hf, hs, he, p, hp, ho, hn⟩
    exact ⟨S, hS, hf, p, hq, hk, hs, he, hp, ho, hn⟩
  · rintro ⟨S, hS, hf, p, hq, hk, hs, he, hp, ho, hn⟩
    exact ⟨hq, hk, S, hS, hf, hs, he, p, hp, ho, hn⟩

theorem theoremA_of_isSimpleGroup [IsSimpleGroup G]
    (ih : TheoremAOnProperSections K G) : TheoremA K G := by
  by_contra hA
  obtain ⟨S, hS, hf, p, h⟩ := not_theoremA_iff.mp hA
  exact h.not_isSimpleGroup ih inferInstance

theorem MinimalCounterexample.simple_case
    (h : MinimalCounterexample K G) (hG : IsSimpleGroup G) :
    ¬ IsMulCommutative G ∧ IsQuasithin G ∧ IsKGroup K G ∧
      (¬ IsTheoremBModel G ∨ (IsStronglyQuasithin G ∧ ¬ IsTheoremCModel G)) := by
  classical
  let := hG
  rcases not_theoremsABC_iff.mp h.1 with hA | hB | hC
  · exact (hA (theoremA_of_isSimpleGroup h.2.theoremA)).elim
  · simp only [TheoremB, not_forall] at hB
    obtain ⟨_, hna, hqt, hk, hb⟩ := hB
    exact ⟨hna, hqt, hk, .inl hb⟩
  · simp only [TheoremC, not_forall] at hC
    obtain ⟨_, hna, hsqt, hk, hc⟩ := hC
    exact ⟨hna, hsqt.quasithin, hk, .inr ⟨hsqt, hc⟩⟩

theorem MinimalCounterexample.nonsimple_case
    (h : MinimalCounterexample K G) (hG : ¬ IsSimpleGroup G) :
    ∃ (S : Type u) (_ : Group S) (_ : Finite S) (p : ℕ),
      CounterexampleToTheoremA K G S p := by
  apply not_theoremA_iff.mp
  intro hA
  exact h.1 ⟨hA, fun hs _ _ _ => (hG hs).elim, fun hs _ _ _ => (hG hs).elim⟩

end CFSG.Quasithin.ChapterA.Section02
