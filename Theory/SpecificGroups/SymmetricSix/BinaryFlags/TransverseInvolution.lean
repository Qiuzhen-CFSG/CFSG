module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

/-!
# A nonorthogonal involution in the natural A₆ action

The even involution (04)(12) moves the distinguished duad {4,5} to {0,5},
whose pairing with it is one. Transitivity on nonzero natural vectors
conjugates this involution to every prescribed point, preserving the exact
natural pairing. Source: Aschbacher–Smith, choice before13.7.10, printedp.941.
-/

@[expose] public section
open BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransverseInvolution
open NaturalGeometry NaturalPairing

private def base : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 4 * Equiv.swap 1 2, by decide⟩
private theorem base_square : base ^ 2 = 1 := by decide
private theorem base_pairing :
    form (pairVector 4 5) (naturalRepresentation (Fin 6) base.val (pairVector 4 5)) = 1 := by
  rw [pairVector_map]
  change form (pairVector 4 5) (pairVector 0 5) = 1
  let a : core (Fin 6) := ⟨Pi.single 4 1 + Pi.single 5 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩
  let b : core (Fin 6) := ⟨Pi.single 0 1 + Pi.single 5 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩
  change naturalPairing (Fin 6) (coreToNatural (Fin 6) a) (coreToNatural (Fin 6) b) = 1
  rw [naturalPairing_apply_core]
  decide

/-- Every nonzero source vector is moved nonorthogonally by an even involution. -/
theorem exists_nonorthogonal_involution (z : natural (Fin 6)) (hz : z ≠ 0) :
    ∃ a : alternatingGroup (Fin 6), a ^ 2 = 1 ∧
      form z (naturalRepresentation (Fin 6) a.val z) = 1 := by
  obtain ⟨g, hg⟩ := NaturalTransport.exists_even_image z hz
  refine ⟨g * base * g⁻¹, ?_, ?_⟩
  · rw [conj_pow, base_square, mul_one, mul_inv_cancel]
  · rw [← hg]
    have he : naturalRepresentation (Fin 6) (g.val * base.val * g.val⁻¹)
        (naturalRepresentation (Fin 6) g.val (pairVector 4 5)) =
        naturalRepresentation (Fin 6) g.val
          (naturalRepresentation (Fin 6) base.val (pairVector 4 5)) := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
    change form (naturalRepresentation (Fin 6) g.val (pairVector 4 5))
      (naturalRepresentation (Fin 6) (g.val * base.val * g.val⁻¹)
        (naturalRepresentation (Fin 6) g.val (pairVector 4 5))) = 1
    rw [he, form_invariant]
    exact base_pairing

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransverseInvolution
