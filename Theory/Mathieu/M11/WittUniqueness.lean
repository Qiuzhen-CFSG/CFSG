module

public import Theory.Mathieu.M11.WittCompletionCertificate
public import Theory.Mathieu.M11.WittSeedNormalization

/-!
# Uniqueness of the small Witt design

Every Steiner system `S(4,5,11)` is isomorphic to the explicit small Witt
design. First relabel the four blocks through a triple to the standard seed.
The kernel-checked completion certificate identifies every design containing
that seed with the explicit model. Composing the two permutations gives the
required relabeling of the original design.

Reference: Hall, *The Theory of Groups*, Theorem 5.8.1; this is the
design-uniqueness route to Mathieu recognition cited by Wong, p. 108.
-/

namespace Sporadic.Mathieu

open Theory.GroupTheory
open scoped Pointwise

/-- Every `S(4,5,11)` is a relabeling of the explicit small Witt design. -/
public theorem m11WittDesign_unique (D : SteinerSystem (Fin 11) 4 5) :
    ∃ e : Equiv.Perm (Fin 11),
      e • (D.blocks : Set (Finset (Fin 11))) =
        (m11WittDesign.blocks : Set (Finset (Fin 11))) := by
  obtain ⟨e, D', hblocks, hseed⟩ := exists_relabel_m11CompletionSeed D
  obtain ⟨f, hf⟩ := m11_completion_equiv D' hseed
  have hblocks' : (D'.blocks : Set (Finset (Fin 11))) =
      e • (D.blocks : Set (Finset (Fin 11))) := by
    rw [hblocks]
    ext B
    simp
  refine ⟨f * e, ?_⟩
  rw [mul_smul, ← hblocks']
  exact hf

end Sporadic.Mathieu
