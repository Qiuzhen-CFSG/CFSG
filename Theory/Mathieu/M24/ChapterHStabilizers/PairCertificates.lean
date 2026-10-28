module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# Centralizer words for the two native involution classes

For each point moved by either marked involution, a word in the certified M24
standard generators centralizes that involution and takes a chosen moved point
to the requested point. Two further words send the chosen transposed pair to
{0,9}. These identities let ambient conjugators be corrected inside the marked
pair stabilizer. Only 40 centralizing words, each of length at most 43, are used.

The untrusted search is recorded in `source/generate_pairs.py`. All commutation,
point-transport and marking equations below are checked by the Lean kernel.

Source: Aschbacher–Smith H.14.4(4), printed p.398 (PDF p.409).
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers
open Subgroup
namespace Sporadic.Mathieu.M24ChapterHStabilizers.PairCertificates
open FusionData

def baseMoved (a : Bool) : Fin 24 := if a then 6 else 0

private def transportWord : Bool → Fin 24 → List (Fin 3)
  | false => ![[],[2,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,2,0,1],[2,0,2,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,2,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,1],[2,0,1,0,2,0,1,0,1,0,1,0,1,0,1,0,1,0,2,0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,1],[1,0,2,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,2],[1,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,2,0,1],[1,0,2,0,1,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,1,0,2,0,2,0,2],[2,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,1],[1,0,1,0,1,0,1,0,2,0,2,0,2,0,2,0,1,0,1,0,1,0,1,0,2,0,2,0,2,0,2,0,1,0,1,0,1,0,1],[2,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,1],[2,0,2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,0,1],[2,0,1,0,2,0,1,0,1,0,1,0,2,0,2,0,2,0,2,0,2,0,2,0,1,0,2,0,1,0,1,0,2,0,2,0,2,0,2,0,1,0,2],[1,0,1,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,1,0,2],[2,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,1,0,2,0,1],[1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,1,0,2,0,1,0,1,0,2,0,1,0,2,0,2],[2,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,2,0,1],[2,0,1,0,1,0,2,0,1,0,1,0,2,0,1,0,1],[2,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,1],[2,0,1,0,2,0,2,0,2,0,1,0,2,0,2,0,2,0,1,0,2,0,1,0,1,0,1,0,2,0,1,0,1,0,1,0,2,0,1],[2,0,1,0,2,0,2,0,2,0,2,0,2,0,2,0,2,0,1,0,2,0,1,0,2,0,1,0,2,0,2,0,2,0,1,0,2],[0],[2,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,2,0,2],[1,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,1,0,1],[1,0,2,0,2,0,1,0,2,0,2,0,1,0,2,0,1,0,1,0,2,0,1,0,2,0,2,0,2,0,1,0,1]]
  | true => ![[],[],[],[],[],[],[],[0,2,0,1,0,1,0,1,0,1,0,1,0,2,0,2,0,2,0,2,0,2,0,1,0],[0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0,2,0,2,0,1],[0,1,0,1,0,1,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,1,0,2,0,1],[0,2,0,2,0,2,0,1,0,2,0,2,0,2,0,2,0,1,0,2,0,1],[],[0,2,0,2,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,2,0,2,0,1,0,2,0,1],[1,0,1,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,1,0,1,0,2,0,2,0,1,0,1,0],[2,0,1,0,2,0,1,0,2,0,1,0,2,0,1,0,1,0,2,0,2,0,1,0,1,0,1],[2,0,2,0,1,0,2,0,1,0,1,0,1,0,1,0,1,0,2,0,1,0,1,0,1],[1,0,2,0,2,0,1,0,1,0,2],[],[1,0,2,0,1,0,1,0,1,0,1,1,0,1,0,2,0,2,0,2,0,1,0],[2,0,1,0,2,0,2,0,1,0,2,0,2,0,1,0,1,0,2,0,1,0,2,0,2,0,2,0],[2,0,1,0,2,0,2,0,2,0,2,0,2,0,2,0,1,0,1,0,2,0,2],[2,0,2,0,1,0,1,0,2,0,1,1,0,1,0,1,0,1,0,2,0,2,0],[2,0,1,0,2,0,1,0,1,0,1,0,1,0,2,0,1,0,1,0,1,0],[0,2,0,2,0,2,0,1,0,1,0,2,0,1,0,2,0,1,0,1,0,2,0,1,0,2,0,1]]

private def markingWord : Bool → List (Fin 3)
  | false => [1,0,1,0,1,0,2,0,2]
  | true => [0,2,0,1,0,1,0,2,0,1,0,2,0,2,0]

private theorem commute_checks (a : Bool) : ∀ x y : Fin 24,
    basePoint a x ≠ x →
    wordPoint (transportWord a x) (basePoint a y) =
      basePoint a (wordPoint (transportWord a x) y) := by
  cases a <;> decide +kernel

private theorem transport_checks (a : Bool) : ∀ x : Fin 24,
    basePoint a x ≠ x → wordPoint (transportWord a x) (baseMoved a) = x := by
  cases a <;> decide +kernel

private theorem marking_checks : ∀ a : Bool,
    wordPoint (markingWord a) (baseMoved a) = 0 ∧
    wordPoint (markingWord a) (basePoint a (baseMoved a)) = 9 := by
  decide +kernel

theorem exists_centralizer_transport (a : Bool) (x : Fin 24)
    (hx : (base a).val x ≠ x) :
    ∃ g : M24, g * base a = base a * g ∧ g.val (baseMoved a) = x := by
  refine ⟨evaluate (transportWord a x), ?_, ?_⟩
  · apply Subtype.ext
    apply Equiv.ext
    intro y
    change (evaluate (transportWord a x)).val ((base a).val y) =
      (base a).val ((evaluate (transportWord a x)).val y)
    rw [evaluate_apply, evaluate_apply, base_apply, base_apply]
    exact commute_checks a x y (by rwa [base_apply] at hx)
  · rw [evaluate_apply]
    exact transport_checks a x (by rwa [base_apply] at hx)

noncomputable def marking (a : Bool) : M24 := evaluate (markingWord a)

theorem marking_apply (a : Bool) :
    (marking a).val (baseMoved a) = 0 ∧
    (marking a).val ((base a).val (baseMoved a)) = 9 := by
  simpa only [marking, evaluate_apply, base_apply] using marking_checks a

end Sporadic.Mathieu.M24ChapterHStabilizers.PairCertificates
