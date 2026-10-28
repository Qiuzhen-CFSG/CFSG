module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierCertificate.Checks
import Mathlib.Tactic.FinCases

/-!
# Abstract interpretation of Held's M₁ Schreier data

The checked tree identities make each omitted edge trivial in the abstract
presentation. Every retained symbol is its literal Schreier element
`ρ i * g a * (ρ j)⁻¹`. Their products telescope, proving all 14409 initial
Schreier relators, including the three protected-symbol equations.

The right-action endpoint is identified with the inverse of the evaluated
permutation. The already kernel-checked seven presentation relators therefore
close every relator loop; the three short subgroup loops are checked directly.
No faithfulness of the permutation action is assumed or deduced here.

Membership of all 2062 symbols in the literal source M₁ subgroup then gives
an actual abstract coset cover by the 2058 representatives. This is explicitly
a conditional result: the separate membership proof remains necessary.

Source: John Bray's ATLAS `HeG1-P1.M`, retained with attribution in
`Held/Model/Source/`; the exact tree, symbol numbering and initial words are
specified in `M1Cosets/source/README.md` and `SchreierData.lean`.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Schreier
open Subgroup.CosetWordCertificate

private theorem eval_bridge {G α : Type*} [Group G] (g : α → G) (w : Word α) :
    Theory.GroupTheory.CosetEnumeration.eval g w = eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons, Theory.GroupTheory.CosetEnumeration.eval, List.map_cons, List.prod_cons]
    exact congrArg ((Theory.GroupTheory.CosetEnumeration.letterValue g a) * ·) ih

/-- A positive symbol is its actual Schreier element; tree edges evaluate to one. -/
theorem positiveWord_eval (i : Fin 2058) (a : Fin 2) :
    eval symbol (positiveWord i a) =
      representative i * PresentedGroup.of a * (representative (destination i (a, true)))⁻¹ := by
  have hc := positiveCheck i a
  unfold PositiveCheck at hc
  unfold positiveWord
  dsimp only
  split <;> rename_i hn
  · rw [if_pos hn] at hc
    rw [eval_nil, eq_comm, mul_inv_eq_one]
    rcases hc with hf | hb
    · simp only [representative, hf, eval_append, eval_letter, ↓reduceIte]
    · simp only [representative, hb, eval_append, eval_letter, Bool.false_eq_true, ↓reduceIte]
      simp
  · rw [if_neg hn] at hc
    obtain ⟨hlo, hhi, he⟩ := hc
    rw [eval_letter]
    simp only [↓reduceIte]
    unfold symbol symbolWord
    rw [if_neg hn, if_neg (by omega), if_pos hhi]
    simp only [he, eval_append, eval_invRev, eval_letter, ↓reduceIte]
    rfl

/-- Reversing a negative table edge recovers its starting point. -/
theorem destination_reverse (i : Fin 2058) (a : Fin 2) :
    destination (destination i (a, false)) (a, true) = i := by
  fin_cases a
  · exact atlasA.apply_symm_apply i
  · exact atlasB.symm_apply_apply i

/-- Abstract interpretation of both signs of every table edge. -/
theorem edgeWord_eval (i : Fin 2058) (a : Letter (Fin 2)) :
    eval symbol (edgeWord i a) =
      representative i * eval (PresentedGroup.of : Fin 2 → Presentation) [a] *
        (representative (destination i a))⁻¹ := by
  rcases a with ⟨a, b⟩
  cases b
  · simp only [edgeWord, Bool.false_eq_true, ↓reduceIte, eval_invRev, positiveWord_eval,
      destination_reverse, eval_letter, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  · simpa only [edgeWord, ↓reduceIte, eval_letter] using positiveWord_eval i a

/-- Endpoint of a word in the candidate right-action table. -/
def endpoint (i : Fin 2058) : Word (Fin 2) → Fin 2058
  | [] => i
  | a :: w => endpoint (destination i a) w

/-- Schreier rewriting telescopes in the abstract presented group. -/
theorem traceWord_eval (i : Fin 2058) (w : Word (Fin 2)) :
    eval symbol (traceWord i w) =
      representative i * eval (PresentedGroup.of : Fin 2 → Presentation) w *
        (representative (endpoint i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [traceWord, endpoint]
  | cons a w ih =>
    rw [traceWord, eval_append, edgeWord_eval, ih, endpoint,
      show eval (PresentedGroup.of : Fin 2 → Presentation) (a :: w) =
        eval PresentedGroup.of [a] * eval PresentedGroup.of w from eval_append _ [a] w]
    simp [mul_assoc]

/-- A signed table step is the source right action of its abstract letter. -/
theorem destination_eq (i : Fin 2058) (a : Letter (Fin 2)) :
    destination i a =
      ((representation.comp presentationMap) (eval (PresentedGroup.of : Fin 2 → Presentation) [a]))⁻¹ i := by
  rcases a with ⟨a, b⟩
  cases b <;> fin_cases a <;>
    simp only [eval_letter, Bool.false_eq_true, ↓reduceIte, MonoidHom.comp_apply,
      map_inv, inv_inv, presentationMap_of]
  all_goals rfl

/-- The full word path follows the source right action. -/
theorem endpoint_eq (i : Fin 2058) (w : Word (Fin 2)) :
    endpoint i w =
      ((representation.comp presentationMap) (eval (PresentedGroup.of : Fin 2 → Presentation) w))⁻¹ i := by
  induction w generalizing i with
  | nil => simp [endpoint]
  | cons a w ih =>
    rw [endpoint, ih, destination_eq,
      show eval (PresentedGroup.of : Fin 2 → Presentation) (a :: w) =
        eval PresentedGroup.of [a] * eval PresentedGroup.of w from eval_append _ [a] w,
      map_mul, mul_inv_rev]
    rfl

/-- Each of the seven actual presentation relators closes at every vertex. -/
theorem relator_loop (i : Fin 2058) (r : Fin 7) : endpoint i (relatorWord r) = i := by
  rw [endpoint_eq, relatorWord_eval, map_one, inv_one]
  rfl

/-- The three literal M₁ words close at the marked root. -/
theorem subgroup_loop (r : Fin 3) : endpoint 1205 (subgroupWord r) = 1205 := by
  fin_cases r <;> decide +kernel

/-- The marked root has the empty representative word. -/
theorem representative_root : representative 1205 = 1 := by
  exact eval_nil PresentedGroup.of

/-- Every initial Schreier relator holds in the actual abstract presentation. -/
theorem initialRelator_eval (r : Fin 14409) :
    Theory.GroupTheory.CosetEnumeration.eval symbol (initialRelator r) = 1 := by
  rw [eval_bridge]
  unfold initialRelator
  split <;> rename_i hr
  · rw [eval_reduce, traceWord_eval, relator_loop, relatorWord_eval]
    simp
  · have cases : r.val = 14406 ∨ r.val = 14407 ∨ r.val = 14408 := by omega
    rcases cases with h | h | h <;>
      simp only [h, eval_append, eval_reduce, traceWord_eval, subgroup_loop,
        representative_root, one_mul, inv_one, mul_one, eval_letter]
    all_goals exact mul_inv_cancel _

private theorem symbol_mem_of_bounded (hg : ∀ n : Fin 2062, symbol (n.val + 1) ∈ m1)
    (n : Nat) : symbol n ∈ m1 := by
  by_cases hz : n = 0
  · subst n
    exact m1.one_mem
  by_cases hn : n < 2063
  · have he : n - 1 + 1 = n := by omega
    simpa only [he] using hg ⟨n - 1, by omega⟩
  · have h4 : ¬ n < 4 := by omega
    simpa only [symbol, symbolWord, if_neg hz, if_neg h4, if_neg hn, eval_nil] using m1.one_mem

/-- Membership of the Schreier symbols supplies all abstract coset transitions. -/
def coverOfSymbolMem
    (hg : ∀ n : Fin 2062, symbol (n.val + 1) ∈ m1) :
    Subgroup.GeneratorCosetCover m1 PresentedGroup.of (Fin 2058) where
  repr := representative
  initial := 1205
  initial_eq := representative_root
  step i a := by
    have hm := eval_mem_of_generators_mem m1 symbol (symbol_mem_of_bounded hg) (edgeWord i (a, true))
    refine ⟨⟨_, hm⟩, destination i (a, true), ?_⟩
    simp [edgeWord_eval, mul_assoc]
  inv_step i a := by
    have hm := eval_mem_of_generators_mem m1 symbol (symbol_mem_of_bounded hg) (edgeWord i (a, false))
    refine ⟨⟨_, hm⟩, destination i (a, false), ?_⟩
    simp [edgeWord_eval, mul_assoc]
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Schreier
