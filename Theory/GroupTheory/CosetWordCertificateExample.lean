module

public import Theory.GroupTheory.CosetWordCertificate

/-!
# A small coset-word certificate

This example exercises all six rules, two separately checked chunks, and cover
extraction. An involution belonging to a subgroup has a one-representative cover
for the group it generates. The generic group is not assumed finite.
The defining node is deliberately distinct from the subgroup-loop node.
-/

namespace Subgroup.CosetWordCertificate.Example

open Subgroup.CosetWordCertificate

private def definitions : Definitions Unit where
  parent _ := 0
  letter _ := ((), true)
  parent_lt n := Nat.zero_lt_succ n

private def context : Context Unit where
  parent := definitions.parent
  letter := definitions.letter
  relator _ := [((), true), ((), true)]
  allowed a := a.2

private def facts : Nat → FactData Unit
  | 0 => ⟨0, [], 0⟩
  | 1 => ⟨0, [((), true)], 1⟩
  | 2 => ⟨0, [((), true)], 0⟩
  | 3 => ⟨1, [((), true), ((), true)], 1⟩
  | 4 => ⟨0, [((), false)], 0⟩
  | 5 => ⟨1, [((), false)], 0⟩
  | _ => ⟨0, [], 0⟩

private def instructions : Nat → Instruction Unit
  | 0 => .refl 0
  | 1 => .defining 1
  | 2 => .subgroup ((), true)
  | 3 => .relator 1 0
  | 4 => .reverse 2
  | 5 => .reverse 1
  | _ => .compose 1 5

private theorem firstChunk : checkChunk context facts instructions 0 4 = true := by decide
private theorem secondChunk : checkChunk context facts instructions 4 3 = true := by decide

-- Reject a forward reference, a wrong middle endpoint, and a root definition.
example : check context facts 4 (.reverse 4) (facts 4) = false := by decide
example : check context facts 7 (.compose 1 2) (facts 6) = false := by decide
example : check context facts 7 (.defining 0) (facts 0) = false := by decide

private theorem valid {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (hx : x ∈ H) (hxx : x * x = 1) :
    Valid context H (fun _ : Unit => x) (definitions.repr (fun _ => x)) := by
  apply definitions.valid
  · intro a ha
    have hs : a.2 = true := ha
    simpa only [eval_letter, hs, Bool.true_eq, ↓reduceIte] using hx
  · intro r
    simp [eval_cons, hxx]

/-- A complete two-chunk replay and signed-output extraction in an arbitrary
ambient group. All computation in the example is kernel checked. -/
public def involutionCover {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (hx : x ∈ H) (hxx : x * x = 1) :
    Subgroup.GeneratorCosetCover H (fun _ : Unit => x) Unit := by
  have hC := valid H x hx hxx
  have hfirst := checkChunk_sound hC facts instructions 0 4
    (fun n hn => (Nat.not_lt_zero n hn).elim) firstChunk
  have hall := checkChunk_sound hC facts instructions 4 3 hfirst secondChunk
  exact coverOfFacts facts (fun _ : Unit => 0) () (definitions.repr_zero _)
    (fun _ _ => ()) (fun _ a => if a.2 then 2 else 4)
    (by intro i a; rcases a with ⟨a, b⟩; cases a; cases b <;> rfl)
    (by intro i a; apply hall; cases a.2 <;> decide)

end Subgroup.CosetWordCertificate.Example
