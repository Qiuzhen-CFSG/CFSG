module

public import Theory.Mathieu.M12.Recognition.WittUniqueness.Normalization
public import Theory.Mathieu.M12.Recognition.WittUniqueness.CompletionCertificate

/-!
# Uniqueness of the twelve-point Witt design

Every `S(5,6,12)` is isomorphic to the concrete Witt design. Deriving at point
zero and applying small Witt uniqueness normalizes the 66 blocks through zero.
A kernel-checked finite certificate then shows that every remaining block is a
concrete Witt hexad. Inclusion of two Steiner systems with the same parameters
is equality, giving the required permutation of the original design.

This unconditional geometric uniqueness result supplies the design premise in
the sharp degree-twelve recognition argument. Source context: Aschbacher,
*Sporadic Groups*, Exercise 6.6(6–7), printed p. 95; *A 2-local characterization
of M12*, Illinois J. Math. 47 (2003), Lemma 4.11.
-/

namespace Sporadic.Mathieu

open Theory.GroupTheory
open scoped Pointwise

/-- Every `S(5,6,12)` is a relabeling of the concrete twelve-point Witt design. -/
public theorem m12WittDesign_unique (D : SteinerSystem (Fin 12) 5 6) :
    ∃ e : Equiv.Perm (Fin 12),
      e • (D.blocks : Set (Finset (Fin 12))) =
        (m12WittDesign.blocks : Set (Finset (Fin 12))) := by
  obtain ⟨e, he⟩ := M12WittUniqueness.exists_relabel_augmented D
  have hblocks := M12WittUniqueness.blocks_eq_of_augmented (D.relabel e) he
  refine ⟨e, ?_⟩
  simpa only [SteinerSystem.relabel_blocks, Finset.coe_smul_finset] using
    congrArg (fun s : Finset (Finset (Fin 12)) => (s : Set (Finset (Fin 12)))) hblocks

end Sporadic.Mathieu
