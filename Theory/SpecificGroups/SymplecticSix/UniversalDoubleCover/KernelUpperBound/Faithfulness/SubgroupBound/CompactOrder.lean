module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Checked
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape

/-!
# The compact presentation has order at most 40320

Three commuting square-one generators give a subgroup of order at most eight.
The kernel-checked coset-word certificate supplies 5040 representatives and all
signed generator transitions in the literal presentation. The resulting
surjection from the subgroup times the representatives proves finiteness and
8 · 5040 = 40320 as an upper bound.

The proof uses no matrix or permutation identification, and no externally
computed group order. The 99983 deductions and 80640 output checks are described
in `CompactOrder/source/README.md`.

Source: the exact 51 relators of `CompactData.lean`, extracted from ATLAS
`S62G1-P1.M`. The independent lifting into the raw Schreier presentation is not
needed for this order bound.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
namespace CompactOrder
open Subgroup.CosetWordCertificate

private theorem transitions (i : Fin 5040) (a : Fin 16) :
    Holds smallSubgroup generator (definitions.repr generator)
      ⟨repCode i.val, [decode a.val], repCode (destination (16*i.val+a.val)).val⟩ := by
  have hs := (factBEq_eq_true_iff _ _).mp (all_shapes (16*i.val+a.val) (by omega))
  have hd : (16*i.val+a.val) / 16 = i.val := by omega
  have hm : (16*i.val+a.val) % 16 = a.val := by omega
  change facts (output (16*i.val+a.val)) = _ at hs
  rw [hd, hm] at hs
  rw [← hs]
  exact all_hold _ (output_lt _)

private theorem decode_even (a : Fin 8) : decode (2*a.val) = (a, true) := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [decode]
    omega
  · simp [decode]

private theorem decode_odd (a : Fin 8) : decode (2*a.val+1) = (a, false) := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [decode]
    omega
  · simp [decode, Nat.add_mod]

/-- Checked subgroup-witness transitions for all eight generators and inverses. -/
def compactCover : Subgroup.GeneratorCosetCover smallSubgroup generator (Fin 5040) where
  repr i := definitions.repr generator (repCode i.val)
  initial := 0
  initial_eq := by
    have hr : repCode 0 = 0 := by decide +kernel
    change definitions.repr generator (repCode 0) = 1
    rw [hr]
    exact definitions.repr_zero generator
  step i a := by
    obtain ⟨h, hh⟩ := transitions i ⟨2*a.val, by omega⟩
    refine ⟨h, destination (16*i.val+2*a.val), ?_⟩
    simpa [decode_even] using hh
  inv_step i a := by
    obtain ⟨h, hh⟩ := transitions i ⟨2*a.val+1, by omega⟩
    refine ⟨h, destination (16*i.val+(2*a.val+1)), ?_⟩
    simpa [decode_odd] using hh

end CompactOrder

/-- The literal eight-generator, 51-relator compact presentation is finite,
with order at most 8 · 5040 = 40320. -/
theorem compactPresentation_bound :
    Finite CompactPresentation ∧ Nat.card CompactPresentation ≤ 40320 := by
  let : Finite CompactOrder.smallSubgroup := CompactOrder.small_bound.1
  have h := CompactOrder.compactCover.finite_card_le (PresentedGroup.closure_range_of _)
  refine ⟨h.1, h.2.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 5040 CompactOrder.small_bound.2

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
