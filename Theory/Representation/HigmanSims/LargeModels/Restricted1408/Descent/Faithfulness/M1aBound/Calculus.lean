module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.Data
import Mathlib.Tactic.FinCases

/-! Schreier rewriting telescopes in any group. The finite word checks imply
all 1,300 relators in the literal HS presentation, without assuming a faithful
permutation action. Source: the elementary Reidemeister–Schreier argument,
applied to ATLAS HSG1-P1.M. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
open Subgroup.CosetWordCertificate

def expand (f : Fin 101 → Word Bool) : Word (Fin 101) → Word Bool
  | [] => []
  | (a, b) :: w => (if b then f a else FreeGroup.invRev (f a)) ++ expand f w

theorem eval_expand {G : Type*} [Group G] (g : Bool → G)
    (f : Fin 101 → Word Bool) (w : Word (Fin 101)) :
    eval g (expand f w) = eval (fun a => eval g (f a)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, b⟩
    cases b <;> simp [expand, eval_append, eval_cons, eval_invRev, ih]

abbrev EdgeCheck (i : Fin 100) (a : Letter Bool) : Prop :=
    reduce (expand edgeWord (transitionWord i a)) =
    reduce (representative i ++ [a] ++ FreeGroup.invRev (representative (next i a)))

theorem eval_transition {G : Type*} [Group G] (g : Bool → G)
    (i : Fin 100) (a : Letter Bool) (h : EdgeCheck i a) :
    eval (fun k => eval g (edgeWord k)) (transitionWord i a) =
      eval g (representative i) * eval g [a] * (eval g (representative (next i a)))⁻¹ := by
  rw [← eval_expand, ← eval_reduce, h, eval_reduce, eval_append, eval_append,
    eval_invRev]

theorem eval_rewrite {G : Type*} [Group G] (g : Bool → G)
    (h : ∀ i a, EdgeCheck i a) (i : Fin 100) (w : Word Bool) :
    eval (fun k => eval g (edgeWord k)) (rewrite i w) =
      eval g (representative i) * eval g w * (eval g (representative (terminal i w)))⁻¹ := by
  induction w generalizing i with
  | nil => simp [rewrite, terminal]
  | cons a w ih =>
    simp only [rewrite, eval_append, eval_transition g _ _ (h _ _), ih, terminal]
    rw [show eval g (a :: w) = eval g [a] * eval g w from eval_append g [a] w]
    simp [mul_assoc]

theorem eval_sourceWord {G : Type*} [Group G] (g : Bool → G) (r : Fin 13) :
    eval g (sourceWord r) = word (g false) (g true) r := by
  simp only [sourceWord, eval, FreeGroup.lift_mk, List.map_map, word]
  congr 2
  funext j
  fin_cases j <;> simp [letter]

def edgeGenerator (k : Fin 101) : Universal := eval generator (edgeWord k)

theorem relator_valid_of_checks (he : ∀ i a, EdgeCheck i a)
    (hl : ∀ i r, terminal i (sourceWord r) = i) (i : Fin 100) (r : Fin 13) :
    eval edgeGenerator (relatorWord i r) = 1 := by
  change eval (fun k => eval generator (edgeWord k)) (rewrite i (sourceWord r)) = 1
  rw [eval_rewrite generator he, eval_sourceWord,
    universal_word, hl]
  simp

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
