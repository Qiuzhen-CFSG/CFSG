module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactOrder.Checked
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactOrder.Shape

/-!
# The compact Rudvalis max4 presentation has order at most 2048

Two commuting square-one generators give a subgroup of order at most four.
The kernel-checked coset certificate proves all signed generator transitions
for 512 representatives in the literal eleven-generator presentation.
The resulting cover proves finiteness and the bound 4 · 512 = 2048.

The 11811 deductions and 11264 output checks are described in
`CompactOrder/source/README.md`. This proof uses precisely the relations of
`CompactData.lean`; it assumes neither compact lifting nor a model isomorphism.
The source context is the original Rudvalis max4 presentation used in the
local calculation supporting Aschbacher–Smith I.1.3(1), printed p.407.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
namespace CompactOrder
open Subgroup.CosetWordCertificate

private theorem transitions (i : Fin 512) (a : Fin 22) :
    Holds smallSubgroup generator (definitions.repr generator)
      ⟨repCode i.val, [decode a.val], repCode (destination (22*i.val+a.val)).val⟩ := by
  have hs := (factBEq_eq_true_iff _ _).mp (all_shapes (22*i.val+a.val) (by omega))
  have hd : (22*i.val+a.val) / 22 = i.val := by omega
  have hm : (22*i.val+a.val) % 22 = a.val := by omega
  change facts (output (22*i.val+a.val)) = _ at hs
  rw [hd, hm] at hs
  rw [← hs]
  exact all_hold _ (output_lt _)

private theorem decode_even (a : Fin 11) : decode (2*a.val) = (a, true) := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [decode]
    omega
  · simp [decode]

private theorem decode_odd (a : Fin 11) : decode (2*a.val+1) = (a, false) := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [decode]
    omega
  · simp [decode, Nat.add_mod]

/-- Checked subgroup-witness transitions for all eleven generators and inverses. -/
def compactCover : Subgroup.GeneratorCosetCover smallSubgroup generator (Fin 512) where
  repr i := definitions.repr generator (repCode i.val)
  initial := 0
  initial_eq := by
    have hr : repCode 0 = 0 := by decide +kernel
    change definitions.repr generator (repCode 0) = 1
    rw [hr]
    exact definitions.repr_zero generator
  step i a := by
    obtain ⟨h, hh⟩ := transitions i ⟨2*a.val, by omega⟩
    refine ⟨h, destination (22*i.val+2*a.val), ?_⟩
    simpa [decode_even] using hh
  inv_step i a := by
    obtain ⟨h, hh⟩ := transitions i ⟨2*a.val+1, by omega⟩
    refine ⟨h, destination (22*i.val+(2*a.val+1)), ?_⟩
    simpa [decode_odd] using hh

end CompactOrder

/-- The literal eleven-generator, 159-relator compact presentation is finite,
with order at most 4 · 512 = 2048. -/
theorem compactPresentation_bound :
    Finite CompactPresentation ∧ Nat.card CompactPresentation ≤ 2048 := by
  let : Finite CompactOrder.smallSubgroup := CompactOrder.small_bound.1
  have h := CompactOrder.compactCover.finite_card_le (PresentedGroup.closure_range_of _)
  refine ⟨h.1, h.2.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 512 CompactOrder.small_bound.2

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
