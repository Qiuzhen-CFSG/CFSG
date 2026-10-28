module

public import Theory.Representation.BinaryPermutation
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The binary permutation module for the alternating group

The full module is `Fin n → ZMod 2`, its core is the augmentation kernel,
and its natural section is the image of the core modulo the constant line.
The augmentation of the all-one vector proves the odd-degree splitting and
the dimensions in both parities.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), §B.3, Lemma B.3.1, printed p. 83.

The residual-image transport used for the corrected B.3.4 application in
13.2.2(4) is re-exported from `PResidual.FiniteImage`. In particular,
`Subgroup.map_embedded_pResidual` identifies the image of `O²(M₁)` with
the residual of the image stabilizer. The concrete flag and offender
calculations required to establish its full commutator action are separate.
-/

public section

namespace CFSG.Quasithin.ChapterB

open BinaryPermutation Module

/-- B.3.1(2): the odd-degree splitting, dimension, and equivariant identification
of the core with the natural module. The identification respects even the full
symmetric group action. -/
theorem lemma_B_3_1_2 {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n) :
    IsCompl (core (Fin n)) (constants (Fin n)) ∧
    finrank (ZMod 2) (natural (Fin n)) = n - 1 ∧
    ∃ e : core (Fin n) ≃ₗ[ZMod 2] natural (Fin n),
      ∀ (g : Equiv.Perm (Fin n)) (v : core (Fin n)),
        e (coreRepresentation (Fin n) g v) =
          naturalRepresentation (Fin n) g (e v) := by
  have : NeZero n := ⟨by omega⟩
  have h : Odd (Fintype.card (Fin n)) := by simpa using hodd
  exact ⟨core_isCompl_constants _ h, by simpa using finrank_natural_odd (Fin n) h,
    coreEquivNatural _ h, coreEquivNatural_equivariant _ h⟩

/-- The strict inclusions and natural-module dimension in the even-degree case
of B.3.1(3). The assertion that this is the unique chief series is separate. -/
theorem lemma_B_3_1_even_dimensions {n : ℕ} (hn : 5 ≤ n) (heven : Even n) :
    constants (Fin n) < core (Fin n) ∧ core (Fin n) < ⊤ ∧
      finrank (ZMod 2) (natural (Fin n)) = n - 2 := by
  have : NeZero n := ⟨by omega⟩
  have h : Even (Fintype.card (Fin n)) := by simpa using heven
  exact ⟨constants_lt_core _ h (by simpa using (show 4 ≤ n by omega)),
    core_lt_top _, by simpa using finrank_natural_even (Fin n) h⟩

end CFSG.Quasithin.ChapterB
