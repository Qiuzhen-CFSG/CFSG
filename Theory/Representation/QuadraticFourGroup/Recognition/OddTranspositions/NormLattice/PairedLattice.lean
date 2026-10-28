module

public import Theory.GroupTheory.PairedProduct.Lattice
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates

/-!
# The norm-diagonal lattice in the actual component-pair coordinates

Given `NormPairCoordinates h`, the paired diagonal in the literal coordinates
on `E/Z(E)` is self-normalizing and maximal among proper subgroups invariant
under the transported source four-group action. Simplicity and perfectness of
`L/Z(L)` follow from the original component hypothesis. Pair transitivity comes
from the coordinate witness, while diagonal invariance is already proved from
its norm-image identity and the actual conjugation action.

These are the coordinate conclusions used in GLS2, Theorem 25.14, Step 2,
via Chapter B, Lemma 3.25. Construction of the coordinate witness and transport
back to the ambient group belong to the surrounding source assembly.
-/

public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}
  {h : Hypotheses ρ L B a}

/-- Self-normalization of the actual norm image in the supplied coordinates. -/
theorem NormPairCoordinates.diagonal_self_normalizing (d : NormPairCoordinates h) :
    normalizer (PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L) :
        Set (Fin d.pairCount → (L ⧸ center L) × (L ⧸ center L))) =
      PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L) := by
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact PairedProduct.normalizer_diagonal

/-- The exact transported B-action admits no invariant intermediate subgroup
strictly between the norm image and the full coordinate product. -/
theorem NormPairCoordinates.invariant_intermediate_eq_diagonal_or_top
    (d : NormPairCoordinates h)
    {M : Subgroup (Fin d.pairCount → (L ⧸ center L) × (L ⧸ center L))}
    (hD : PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L) ≤ M)
    (hM : ∀ b : B, M.map (h.orbitCoordinateAction d.equiv b).toMonoidHom = M) :
    M = PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L) ∨ M = ⊤ := by
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact PairedProduct.eq_diagonal_or_eq_top d.pair_transitive hD hM

/-- Properness, invariance and maximality of the norm image for the actual
source action, with no additional group-theoretic premises on the coordinates. -/
theorem NormPairCoordinates.diagonal_maximal_invariant [Finite G]
    (d : NormPairCoordinates h) :
    Maximal (fun M : Subgroup (Fin d.pairCount → (L ⧸ center L) × (L ⧸ center L)) =>
      M ≠ ⊤ ∧ ∀ b : B, M.map (h.orbitCoordinateAction d.equiv b).toMonoidHom = M)
      (PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L)) := by
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nonempty (Fin d.pairCount) := ⟨⟨0, d.pairCount_pos⟩⟩
  exact PairedProduct.diagonal_maximal_invariant d.pair_transitive d.diagonal_invariant

end Representation.QuadraticFourGroup

end
