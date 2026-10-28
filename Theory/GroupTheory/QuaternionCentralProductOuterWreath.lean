module

public import Theory.GroupTheory.CyclicFourSubgroupAction
public import Theory.GroupTheory.PermutationWreathEmbedding
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Frattini

/-!
# Descent of the quaternion-axis action to the Frattini outer image

The six quaternion axes in a central product of two quaternion groups form
two triples, one in each intrinsic factor. Permuting the axes gives the
`S₃ ≀ C₂` action, and `S₃ ≃ SL₂(2)` gives the desired matrix coordinates.
If its kernel is precisely the kernel of the Frattini quotient action,
the first isomorphism theorem transfers the embedding to the actual range
of `quotientAut (frattini H)`.

The theorem here is the assembly step with the two geometric inputs explicit:
a numbering of the axes which respects the pair of triples, and equality of
the two action kernels. It does not assume that either input follows for an
arbitrary group. The central-product application must discharge both inputs.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup

/-- Transfer the intrinsic axis action to the concrete Frattini automorphism
image, once its block structure and exact kernel have been established. -/
public theorem exists_frattini_outer_wreath_embedding_of_cyclicFour_coordinates
    {H : Type*} [Group H]
    (e : CyclicFourSubgroups H ≃ (Fin 3 × Multiplicative (ZMod 2)))
    (hblocks : ∀ a : MulAut H, ∃ q : Multiplicative (ZMod 2),
      ∀ D : CyclicFourSubgroups H, (e (cyclicFourAction a D)).2 = q * (e D).2)
    (hker : (quotientAut (frattini H)).ker =
      (cyclicFourAction (G := H)).ker) :
    ∃ f : (quotientAut (frattini H)).range →*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (Multiplicative (ZMod 2)), Function.Injective f := by
  obtain ⟨f, hf⟩ := RegularWreathProduct.exists_embedding_range_of_two_blocks
    (cyclicFourAction (G := H)) e hblocks
  let eker := MonoidHom.rangeEquivOfKerEq (quotientAut (frattini H))
    (cyclicFourAction (G := H)) hker
  exact ⟨f.comp eker.toMonoidHom, hf.comp eker.injective⟩

end Subgroup
