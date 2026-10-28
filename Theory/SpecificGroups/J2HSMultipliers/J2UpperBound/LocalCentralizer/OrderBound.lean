module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Checked
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Shape

/-!
# The normalized J₂ local presentation is finite of order at most 3840

The kernel-checked coset-word replay supplies 3840 representatives modulo the
trivial subgroup and every signed generator transition in the literal group.
Induction on words gives a surjection from this finite family, proving both
finiteness and the upper bound. No permutation quotient or external group
order is used. See `OrderBound/source/README.md` for certificate provenance,
reproduction and measurements.

Source application: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407/PDF p.418.
The local universal-kernel application is in `OrderBound/Consumer.lean`;
the global multiplier assembly remains with the parent module.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
namespace OrderBound
open Subgroup.CosetWordCertificate

private theorem transitions (i : Fin 3840) (a : Fin 4) :
    Holds (⊥ : Subgroup Presentation) generator (definitions.repr generator)
      ⟨repCode i.val, [decode a.val], repCode (destination (4*i.val+a.val)).val⟩ := by
  have hs := (factBEq_eq_true_iff _ _).mp (all_shapes (4*i.val+a.val) (by omega))
  have hd : (4*i.val+a.val) / 4 = i.val := by omega
  have hm : (4*i.val+a.val) % 4 = a.val := by omega
  change facts (output (4*i.val+a.val)) = _ at hs
  rw [hd, hm] at hs
  rw [← hs]
  exact all_hold _ (output_lt _)

private def generatorIndex : Bool → Nat
  | false => 0
  | true => 1

private theorem generatorIndex_lt (a : Bool) : generatorIndex a < 2 := by
  cases a <;> decide

private theorem decode_even (a : Bool) : decode (2 * generatorIndex a) = (a, true) := by
  cases a <;> rfl

private theorem decode_odd (a : Bool) : decode (2 * generatorIndex a + 1) = (a, false) := by
  cases a <;> rfl

/-- Actual trivial-subgroup transitions for both generators and their inverses. -/
def presentationCover : Subgroup.GeneratorCosetCover (⊥ : Subgroup Presentation) generator (Fin 3840) where
  repr i := definitions.repr generator (repCode i.val)
  initial := 0
  initial_eq := by
    have hr : repCode 0 = 0 := by decide +kernel
    change definitions.repr generator (repCode 0) = 1
    rw [hr]
    exact definitions.repr_zero generator
  step i a := by
    have ha := generatorIndex_lt a
    obtain ⟨h, hh⟩ := transitions i ⟨2*generatorIndex a, by omega⟩
    refine ⟨h, destination (4*i.val+2*generatorIndex a), ?_⟩
    simpa [decode_even] using hh
  inv_step i a := by
    have ha := generatorIndex_lt a
    obtain ⟨h, hh⟩ := transitions i ⟨2*generatorIndex a+1, by omega⟩
    refine ⟨h, destination (4*i.val+(2*generatorIndex a+1)), ?_⟩
    simpa [decode_odd] using hh

end OrderBound

/-- The exact sixteen-relator presentation is finite and has order at most 3840. -/
theorem presentation_finite_card_le : Finite Presentation ∧ Nat.card Presentation ≤ 3840 := by
  let : Subsingleton (⊥ : Subgroup Presentation) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.mp a.property).trans
      (Subgroup.mem_bot.mp b.property).symm)⟩
  have h := OrderBound.presentationCover.finite_card_le (PresentedGroup.closure_range_of _)
  simpa only [Nat.card_unique, Nat.card_fin, one_mul] using h

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
