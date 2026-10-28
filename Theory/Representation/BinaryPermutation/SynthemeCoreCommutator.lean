module
public import Theory.Representation.BinaryPermutation.SynthemeCoreWeights

/-!
# Weight four in the tetrahedral residual commutator

The Klein four subgroup of A₄ fixes words constant on opposite edges of
its tetrahedron. Displacements of those words lie in the even plane on
these three edge pairs. Every nonzero word in that plane has weight four;
conversely a fixed weight-four word is a sum of two of its own displacements.
The certificates enumerate only 64 words and the twelve tetrahedral actors.

The original five-dimensional core application retains its actual component
quotient and plane residual in Chapter13/Section04/FixedCoreSource/Nonsolvable.
Source: Aschbacher–Smith 13.4.14, first paragraph of the proof, printed p.911.
-/

public section
open Subgroup
namespace BinaryPermutation.SynthemeCoreChief
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype A := Subtype.fintype _

/-- The even plane of words constant on opposite tetrahedral edges. -/
def oppositePlane : AddSubgroup (core (Fin 6)) where
  carrier := {w | w.val 0 = w.val 1 ∧ w.val 2 = w.val 3 ∧ w.val 4 = w.val 5 ∧
    w.val 0 + w.val 2 + w.val 4 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨congrArg₂ (· + ·) hx.1 hy.1, congrArg₂ (· + ·) hx.2.1 hy.2.1,
      congrArg₂ (· + ·) hx.2.2.1 hy.2.2.1, ?_⟩
    change (x.val 0 + y.val 0) + (x.val 2 + y.val 2) + (x.val 4 + y.val 4) = 0
    calc
      _ = (x.val 0 + x.val 2 + x.val 4) + (y.val 0 + y.val 2 + y.val 4) := by abel
      _ = 0 := by rw [hx.2.2.2,hy.2.2.2,add_zero]
  neg_mem' := by
    intro x hx
    refine ⟨congrArg Neg.neg hx.1,congrArg Neg.neg hx.2.1,congrArg Neg.neg hx.2.2.1,?_⟩
    change -x.val 0 + -x.val 2 + -x.val 4 = 0
    rw [←neg_add,←neg_add,hx.2.2.2,neg_zero]

private theorem moved_test : ∀ w : Fin 6 → ZMod 2,
    (∀ k : A, k ∈ klein → (fun i => w ((synthemeHom k).symm i)) = w) →
    ∀ a : A, let v := (fun i => w ((synthemeHom a).symm i) - w i)
      v 0 = v 1 ∧ v 2 = v 3 ∧ v 4 = v 5 ∧ v 0 + v 2 + v 4 = 0 := by
  decide +kernel

private theorem plane_weight_test : ∀ w : Fin 6 → ZMod 2,
    w 0 = w 1 → w 2 = w 3 → w 4 = w 5 → w 0 + w 2 + w 4 = 0 →
    w = 0 ∨ wordWeight w = 4 := by decide +kernel

private theorem four_sum_test : ∀ w : Fin 6 → ZMod 2,
    (∀ k : A, k ∈ klein → (fun i => w ((synthemeHom k).symm i)) = w) →
    wordWeight w = 4 → ∃ a b : A,
      (fun i => w ((synthemeHom a).symm i) - w i) +
      (fun i => w ((synthemeHom b).symm i) - w i) = w := by
  decide +kernel

/-- Every tetrahedral displacement of a Klein-fixed word lies in this plane. -/
theorem klein_fixed_displacement (w : core (Fin 6))
    (hw : ∀ k : A, k ∈ klein → coreRepresentation (Fin 6) (synthemeHom k) w = w)
    (a : A) : coreRepresentation (Fin 6) (synthemeHom a) w - w ∈ oppositePlane :=
  moved_test w.val (fun k hk => congrArg Subtype.val (hw k hk)) a

/-- The plane has only zero and weight-four words. -/
theorem oppositePlane_weight (w : core (Fin 6)) (hw : w ∈ oppositePlane) :
    w = 0 ∨ wordWeight w.val = 4 := by
  rcases plane_weight_test w.val hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr h

/-- A Klein-fixed weight-four word is a sum of two of its own displacements. -/
theorem weight_four_displacement_sum (w : core (Fin 6))
    (hw : ∀ k : A, k ∈ klein → coreRepresentation (Fin 6) (synthemeHom k) w = w)
    (hweight : wordWeight w.val = 4) : ∃ a b : A,
      (coreRepresentation (Fin 6) (synthemeHom a) w - w) +
      (coreRepresentation (Fin 6) (synthemeHom b) w - w) = w := by
  obtain ⟨a,b,hab⟩ := four_sum_test w.val
    (fun k hk => congrArg Subtype.val (hw k hk)) hweight
  exact ⟨a,b,Subtype.ext hab⟩

end BinaryPermutation.SynthemeCoreChief
