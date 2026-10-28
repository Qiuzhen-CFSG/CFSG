module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts

/-!
# Bounded order checks for the short-element catalogue

A boolean implication skips negative catalogue entries. The positive entries
are checked on the certified three-point base by `orderTest`. Splitting the
normal-form index into 32 blocks of 64 proves that the checks cover every
entry, without enumerating the ambient product in a list-membership test.

Source: Parrott (1972), section 5, p.683; the parent source READMEs.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.OrderChecks

/-- Check exactly the positive entries of the existing catalogue. -/
def entryTest (n : Fin 2048) (c : Fin 15) : Bool :=
  !inCatalogue n c || orderTest n (shortIndex c)

/-- The quotient and remainder decomposition covers all normal-form indices. -/
theorem of_blocks (c : Fin 15)
    (h : ∀ (b : Fin 32) (j : Fin 64), entryTest (blockIndex b j) c = true)
    (n : Fin 2048) : entryTest n c = true := by
  have hn : n = blockIndex ⟨n.val / 64, by omega⟩ ⟨n.val % 64, by omega⟩ := by
    apply Fin.ext
    simp only [blockIndex]
    omega
  rw [hn]
  exact h _ _

/-- A checked positive entry proves order thirteen in the literal Atlas group. -/
theorem entryTest_sound (n : Fin 2048) (c : Fin 15)
    (h : entryTest n c = true) (hc : inCatalogue n c = true) :
    orderOf (shortElement n (shortIndex c)) = 13 := by
  apply orderTest_sound
  simpa only [entryTest, hc, Bool.not_true, Bool.false_or] using h

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.OrderChecks
