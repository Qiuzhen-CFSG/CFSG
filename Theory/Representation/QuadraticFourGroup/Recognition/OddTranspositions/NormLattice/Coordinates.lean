module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.DiagonalModel
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PairedProduct

/-!
# Coordinates for the component pairs of a norm diagonal

The shared interface uses the literal quotient `E/Z(E)` and transports the
actual B-conjugation action through an isomorphism. Its norm-image identity
identifies the given norm subgroup with the product of pair diagonals, and
its transitivity assertion concerns the full pair subgroups. No maximality,
normalizer, or commutator conclusion is included in the interface.

There are one or two pairs, corresponding to the two- and four-component
orbits in GLS2, Theorem 25.14, Step 2. Constructing these coordinates and
proving the paired-product lattice theorem are independent obligations.
-/

@[expose] public section

open Subgroup Theory.GroupTheory


namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

def Hypotheses.orbitConjugation (_h : Hypotheses ρ L B a) :
    B →* MulAut (componentOrbit L B) :=
  (componentOrbit L B).normalizerMonoidHom.comp
    (inclusion (le_normalizer_componentOrbit L B))

def Hypotheses.orbitCoordinateAction (h : Hypotheses ρ L B a)
    {P : Type*} [Group P]
    (e : componentOrbit L B ⧸ center (componentOrbit L B) ≃* P) : B →* MulAut P :=
  (MulAut.centralQuotientAction e).comp h.orbitConjugation

/-- Coordinates on the literal central quotient, identifying the actual norm
image and the actual conjugation action on its component pairs. -/
structure NormPairCoordinates (h : Hypotheses ρ L B a) where
  pairCount : ℕ
  pairCount_pos : 0 < pairCount
  pairCount_le_two : pairCount ≤ 2
  equiv : componentOrbit L B ⧸ center (componentOrbit L B) ≃*
    (Fin pairCount → (L ⧸ center L) × (L ⧸ center L))
  norm_image : (h.normDiagonal.subgroupOf (componentOrbit L B)).map
    (equiv.toMonoidHom.comp (QuotientGroup.mk' (center (componentOrbit L B)))) =
      PairedProduct.diagonal (Fin pairCount) (L ⧸ center L)
  pair_transitive : PairedProduct.IsPairTransitive (Fin pairCount) (L ⧸ center L)
    (h.orbitCoordinateAction equiv)

theorem Hypotheses.orbitCoordinateAction_apply (h : Hypotheses ρ L B a)
    {P : Type*} [Group P]
    (e : componentOrbit L B ⧸ center (componentOrbit L B) ≃* P)
    (b : B) (x : componentOrbit L B) :
    h.orbitCoordinateAction e b (e (QuotientGroup.mk' (center (componentOrbit L B)) x)) =
      e (QuotientGroup.mk' (center (componentOrbit L B)) (h.orbitConjugation b x)) :=
  MulAut.centralQuotientAction_apply e (h.orbitConjugation b) x

/-- The norm image in the published coordinates is invariant under the
transported source action; it is not a new premise of the coordinate model. -/
theorem NormPairCoordinates.diagonal_invariant [Finite G]
    {h : Hypotheses ρ L B a} (d : NormPairCoordinates h) (b : B) :
    (PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L)).map
        (h.orbitCoordinateAction d.equiv b).toMonoidHom =
      PairedProduct.diagonal (Fin d.pairCount) (L ⧸ center L) := by
  rw [← d.norm_image]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨h.orbitConjugation b x, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (h.normDiagonal_normalized b.property) (x : G)).mp hx
    · exact (h.orbitCoordinateAction_apply d.equiv b x).symm
  · rw [card_map_of_injective
      (f := (h.orbitCoordinateAction d.equiv b).toMonoidHom)
      (h.orbitCoordinateAction d.equiv b).injective]

end Representation.QuadraticFourGroup

end
