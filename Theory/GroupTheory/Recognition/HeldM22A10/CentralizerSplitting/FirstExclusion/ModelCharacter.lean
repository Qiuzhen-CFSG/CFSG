module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.Pattern

/-!
# The concrete character and transfer root in the first nonsplit model

Each generator changes the parity of every point by a constant. This property
is closed under multiplication and inversion, giving a binary character on the
actual generated subgroup of permutations of `Fin 16`. The word A³B² has
nontrivial character, and its square is a nonidentity central involution.
These assertions are proved from the published permutation tables.

`ModelFacts` states the remaining intrinsic finite checks; `pattern_of_modelFacts`
feeds those checks to the ambient transfer criterion. No instance of
`ModelFacts` is asserted here.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314. The word and the
parity coordinates are independent choices for the published permutation model.
-/

namespace Theory.GroupTheory.HeldM22A10.FirstExclusion
open NonsplitModels

private def pointParity (i : Fin 16) : ZMod 2 := (i.val : ZMod 2)

private theorem parity_affine (p : First) (i : Fin 16) :
    pointParity (p.val i) = pointParity i + pointParity (p.val 0) := by
  have h : ∀ q ∈ firstSubgroup, ∀ k : Fin 16,
      pointParity (q k) = pointParity k + pointParity (q 0) := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      rcases hq with rfl | rfl
      · decide +kernel
      · decide +kernel
    | one => decide +kernel
    | mul q r hq hr iq ir =>
      intro k
      change pointParity (q (r k)) = pointParity k + pointParity (q (r 0))
      rw [iq (r k), iq (r 0), ir k, add_assoc]
    | inv q hq iq =>
      intro k
      have h1 := iq (q⁻¹ k)
      have h0 := iq (q⁻¹ 0)
      rw [show q (q⁻¹ k) = k from q.apply_symm_apply k] at h1
      rw [show q (q⁻¹ 0) = 0 from q.apply_symm_apply 0] at h0
      have hz : pointParity (0 : Fin 16) = 0 := rfl
      rw [hz] at h0
      have he : pointParity (q⁻¹ k) + pointParity (q 0) =
          (pointParity k + pointParity (q⁻¹ 0)) + pointParity (q 0) := by
        rw [← h1, add_assoc, ← h0, add_zero]
      exact add_right_cancel he
  exact h p.val p.property i

/-- The common parity change of the sixteen-point permutation. -/
@[expose] public def character : First →* Binary where
  toFun p := Multiplicative.ofAdd (((p.val 0).val : ℕ) : ZMod 2)
  map_one' := rfl
  map_mul' p q := by
    change pointParity (p.val (q.val 0)) = pointParity (p.val 0) + pointParity (q.val 0)
    rw [parity_affine, add_comm]

/-- The explicit fourth root used by order-four transfer. -/
@[expose] public def root : First :=
  ⟨firstA ^ 3 * firstB ^ 2,
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩

/-- The central mark, the square of the explicit transfer root. -/
@[expose] public def mark : First := root ^ 2

public theorem root_sq : root ^ 2 = mark := rfl

public theorem mark_sq : mark ^ 2 = 1 := by
  apply Subtype.ext
  decide +kernel

public theorem mark_ne_one : mark ≠ 1 := by
  intro he
  have hp := congrArg (fun p : First => p.val 0) he
  have hn : mark.val 0 ≠ (1 : Equiv.Perm (Fin 16)) 0 := by decide +kernel
  exact hn hp

public theorem root_character : character root ≠ 1 := by
  decide +kernel

public theorem mark_central : mark ∈ Subgroup.center First := by
  apply Subgroup.mem_center_iff.mpr
  intro p
  apply Subtype.ext
  have h : ∀ q ∈ firstSubgroup, q * mark.val = mark.val * q := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      rcases hq with rfl | rfl
      · decide +kernel
      · decide +kernel
    | one => simp
    | mul q r hq hr iq ir =>
      change Commute (q * r) mark.val
      exact Commute.mul_left iq ir
    | inv q hq iq =>
      exact Commute.inv_left iq
  exact h p.val p.property

/-- The three remaining finite checks on the published carrier and character.
The automorphism condition can be proved by `fixed_of_squareRootCount`: the
mark has 20 square roots and every other nonidentity central element has 12. -/
public structure ModelFacts : Prop where
  center_cases : ∀ w : First, w ∈ Subgroup.center First → w = 1 ∨ w = mark
  kills_involutions : ∀ w : First, w ^ 2 = 1 → character w = 1
  square_centralizers : ∀ w : First, character w = 1 → w ^ 2 ≠ 1 → w ^ 4 = 1 →
    w ^ 2 ≠ mark →
    Nat.card (Subgroup.centralizer ({w ^ 2} : Set First)) = 64 ∧
    ∀ z : Subgroup.centralizer ({w ^ 2} : Set First), (z : First) = mark →
      ∀ a : MulAut (Subgroup.centralizer ({w ^ 2} : Set First)), (a z : First) = mark

/-- Assemble the intrinsic pattern from the three remaining finite checks. -/
public def pattern_of_modelFacts (h : ModelFacts) : Pattern First where
  mark := mark
  mark_sq := mark_sq
  mark_ne_one := mark_ne_one
  mark_central := mark_central
  center_cases := h.center_cases
  character := character
  kills_involutions := h.kills_involutions
  root := root
  root_sq := root_sq
  root_character := root_character
  square_centralizers := h.square_centralizers

end Theory.GroupTheory.HeldM22A10.FirstExclusion
