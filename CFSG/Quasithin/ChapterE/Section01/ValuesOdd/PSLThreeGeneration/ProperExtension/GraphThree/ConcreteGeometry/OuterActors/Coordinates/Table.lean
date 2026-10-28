module
public import Theory.SpecificGroups.PSL3Three.Basic
/-!
# The sixteen inner matrices for the PSL₃(3) graph-extension calculation

This is the explicit SD₁₆ table from `PSL3Three.SylowInvolutions`, reproduced
here because that implementation is private. The multiplication and inverse
identities are small matrix certificates checked by the kernel. The next
module embeds these matrices and inverse transpose into the literal graph
extension, with 32 distinct coordinates.

Source: Aschbacher–Smith E.1.14(7), printed p.214, and Asc82a Lemma 4.11;
the concrete matrix table is reused from this repository's
`Theory/SpecificGroups/PSL3Three/SylowInvolutions.lean`.
-/

public section
open Matrix.PSL3Three
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors
set_option maxRecDepth 10000
@[expose] def twoElement : Fin 16 → SL :=
  ![⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
⟨!![2, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩,
⟨!![1, 0, 0; 0, 1, 1; 0, 1, 2], by decide⟩,
⟨!![2, 0, 0; 0, 1, 2; 0, 2, 0], by decide⟩,
⟨!![1, 0, 0; 0, 2, 0; 0, 0, 2], by decide⟩,
⟨!![2, 0, 0; 0, 0, 2; 0, 2, 2], by decide⟩,
⟨!![1, 0, 0; 0, 2, 2; 0, 2, 1], by decide⟩,
⟨!![2, 0, 0; 0, 2, 1; 0, 1, 0], by decide⟩,
⟨!![2, 0, 0; 0, 1, 0; 0, 1, 2], by decide⟩,
⟨!![1, 0, 0; 0, 1, 2; 0, 2, 2], by decide⟩,
⟨!![2, 0, 0; 0, 2, 2; 0, 0, 1], by decide⟩,
⟨!![1, 0, 0; 0, 0, 1; 0, 2, 0], by decide⟩,
⟨!![2, 0, 0; 0, 2, 0; 0, 2, 1], by decide⟩,
⟨!![1, 0, 0; 0, 2, 1; 0, 1, 1], by decide⟩,
⟨!![2, 0, 0; 0, 1, 1; 0, 0, 2], by decide⟩,
⟨!![1, 0, 0; 0, 0, 2; 0, 1, 0], by decide⟩]

@[expose] def productIndex : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8],
    ![2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9],
    ![3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10],
    ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11],
    ![5, 6, 7, 0, 1, 2, 3, 4, 13, 14, 15, 8, 9, 10, 11, 12],
    ![6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13],
    ![7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14],
    ![8, 11, 14, 9, 12, 15, 10, 13, 0, 3, 6, 1, 4, 7, 2, 5],
    ![9, 12, 15, 10, 13, 8, 11, 14, 1, 4, 7, 2, 5, 0, 3, 6],
    ![10, 13, 8, 11, 14, 9, 12, 15, 2, 5, 0, 3, 6, 1, 4, 7],
    ![11, 14, 9, 12, 15, 10, 13, 8, 3, 6, 1, 4, 7, 2, 5, 0],
    ![12, 15, 10, 13, 8, 11, 14, 9, 4, 7, 2, 5, 0, 3, 6, 1],
    ![13, 8, 11, 14, 9, 12, 15, 10, 5, 0, 3, 6, 1, 4, 7, 2],
    ![14, 9, 12, 15, 10, 13, 8, 11, 6, 1, 4, 7, 2, 5, 0, 3],
    ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4]]

@[expose] def inverseIndex : Fin 16 → Fin 16 :=
  ![0, 7, 6, 5, 4, 3, 2, 1, 8, 13, 10, 15, 12, 9, 14, 11]

theorem twoElement_mul (i j : Fin 16) :
    twoElement (productIndex i j) = twoElement i * twoElement j := by
  apply Subtype.ext
  revert i j
  decide +kernel

theorem twoElement_inv (i : Fin 16) :
    twoElement (inverseIndex i) = (twoElement i)⁻¹ := by
  apply Subtype.ext
  revert i
  decide +kernel



end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors
