module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.Calculus

/-!
# Interpreting checked local words at the literal J₃ generators

The trace retains labels `1` and `6158` for `x` and the literal ATLAS word `z`.
This module connects checked signed words with the six published algebraic
relators. All four missing identities still require their actual derivations.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
open Subgroup.CosetWordCertificate

/-- The fixed labels used by the retained elimination trace. -/
def localWord (i : Fin 6) : Word Nat :=
  expand (fun b : Bool => [(if b then 6158 else 1, true)])
    (LocalPresentation.relatorWord i)

theorem eval_localWord {G : Type*} [Group G] (g : Nat → G) (i : Fin 6) :
    eval g (localWord i) = LocalPresentation.relator (g 1) (g 6158) i := by
  rw [localWord, eval_expand]
  have he : (fun b : Bool => eval g [(if b then 6158 else 1, true)]) =
      (fun b : Bool => if b then g 6158 else g 1) := by
    funext b
    cases b <;> simp
  rw [he, LocalPresentation.relatorWord_eq]

/-- A checked word gives the exact algebraic local relation, including its
literal generator identification. -/
theorem local_relator_of_checked_word (g : Nat → Presentation)
    (hx : g 1 = x) (hz : g 6158 = m1Word x y) (i : Fin 6)
    (h : eval g (localWord i) = 1) :
    LocalPresentation.relator x (m1Word x y) i = 1 := by
  simpa only [eval_localWord, hx, hz] using h

/-- The output word of the retained 88,429-step derivation. The signs are
preserved exactly; the first source relator will identify `x⁻¹` with `x`. -/
def sixthTraceWord : Word Nat :=
  [(6158, false), (1, false), (6158, false), (1, false), (6158, false), (1, true),
   (6158, false), (1, false), (6158, false), (1, false), (6158, false), (1, true)]

/-- The retained derivation's output gives precisely local relator two.
The source involution relation and a cyclic conjugation discharge the signs
and the order of the two factors. -/
theorem local_two_of_checked_word (g : Nat → Presentation)
    (hx : g 1 = x) (hz : g 6158 = m1Word x y)
    (h : eval g sixthTraceWord = 1) :
    LocalPresentation.relator x (m1Word x y) 2 = 1 := by
  have hxx : x * x = 1 := by
    simpa only [relator, pow_two] using presentation_satisfies 0
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have he : eval g sixthTraceWord = ((m1Word x y)⁻¹ * x) ^ 6 := by
    simp [sixthTraceWord, eval_cons, hx, hz, hxi, pow_succ, mul_assoc]
  have h6 : ((m1Word x y)⁻¹ * x) ^ 6 = 1 := he.symm.trans h
  change (x * (m1Word x y)⁻¹) ^ 6 = 1
  calc
    (x * (m1Word x y)⁻¹) ^ 6 = x * ((m1Word x y)⁻¹ * x) ^ 6 * x⁻¹ := by
      simp [pow_succ, mul_assoc]
    _ = 1 := by rw [h6]; simp

/-- Final transport for the four traces. This is conditional until all four
checked identities are supplied; it does not assert `RemainingRelations`. -/
theorem remaining_of_checked_words (g : Nat → Presentation)
    (hx : g 1 = x) (hz : g 6158 = m1Word x y)
    (h : ∀ i : Fin 4, eval g (localWord ⟨i.val + 2, by omega⟩) = 1) :
    RemainingRelations := by
  intro i
  exact local_relator_of_checked_word g hx hz _ (h i)

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
