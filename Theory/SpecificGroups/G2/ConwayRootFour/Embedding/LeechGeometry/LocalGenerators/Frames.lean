module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.FixedDimension

/-!
# The two local construction branches on the Leech fixed space

`LongFrame` specifies the SL₃(4) local group, its graph element, and coordinates
on the literal U-fixed space. `ShortFrame` specifies the remaining short-root
family in those same coordinates, including its actual Conway conjugacy marking.
Neither structure is asserted to be inhabited.

Only single-coordinate vectors need be tested: additivity extends these tests
to every six-tuple. This keeps concrete lattice computations finite without
assuming GF(4)-linearity of a map into the binary Leech quotient.
The proved dimension bound also supplies surjectivity as soon as an injective
additive map has all its single-coordinate images fixed by U.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
The assembly consumer is `LocalGenerators.lean`.
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
open OctonionLocals

/-- An injective additive map from six GF(4) coordinates fills the entire
literal fixed space as soon as its single-coordinate images are U-fixed.
The independent bound `fixedSpace_finrank_le_twelve` supplies saturation. -/
theorem coordinates_range_of_single (c : Six F →+ LeechModTwo)
    (hc : Function.Injective c)
    (hfixed : ∀ j a, c (Pi.single j a) ∈ fixedSpace) (v : LeechModTwo) :
    v ∈ fixedSpace ↔ ∃ w, c w = v := by
  have hm (w : Six F) : c w ∈ fixedSpace := by
    rw [← Finset.univ_sum_single w, map_sum]
    exact Submodule.sum_mem _ (fun j _ => hfixed j (w j))
  let f : Six F → fixedSpace := fun w => ⟨c w, hm w⟩
  have hf : Function.Injective f := fun x y h => hc (congrArg Subtype.val h)
  have hsix : Nat.card (Six F) = 2 ^ 12 := by
    rw [Nat.card_fun, GaloisField.card 2 2 (by decide)]
    norm_num
  have hcard : Nat.card fixedSpace ≤ Nat.card (Six F) := by
    rw [hsix, Module.natCard_eq_pow_finrank (K := Atlas.Codes.Bit), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) fixedSpace_finrank_le_twelve
  have hb : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, le_antisymm (Nat.card_le_card_of_injective f hf) hcard⟩
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := hb.surjective ⟨v, hv⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨w, rfl⟩
    exact hm w

/-- The SL₃(4) and graph part of the construction, using the published scalar
subgroups. The tests include every field value at each coordinate. -/
structure LongFrame where
  long : SL(3,F) →* LeechCentralQuotient
  swap : LeechCentralQuotient
  long_mem : ∀ A, long A ∈ centralizerI
  swap_mem : swap ∈ centralizerI
  coordinates : Six F →+ LeechModTwo
  coordinates_injective : Function.Injective coordinates
  coordinates_range : ∀ v, v ∈ fixedSpace ↔ ∃ w, coordinates w = v
  on_long : ∀ A j a,
    quotientModTwoRepresentation (long A) (coordinates (Pi.single j a)) =
      coordinates (action (generator (Sum.inl (Sum.inl A))) (Pi.single j a))
  on_swap : ∀ j a,
    quotientModTwoRepresentation swap (coordinates (Pi.single j a)) =
      coordinates (action graph (Pi.single j a))

/-- The remaining local A₅ branch, in the coordinates of the chosen long
frame. This retains the genuine marked-conjugacy obligation. -/
structure ShortFrame (L : LongFrame) where
  short : F → LeechCentralQuotient
  short_mem : ∀ a, short a ∈ centralizerI
  on_short : ∀ a j b,
    quotientModTwoRepresentation (short a) (L.coordinates (Pi.single j b)) =
      L.coordinates (action (generator (Sum.inl (Sum.inr a))) (Pi.single j b))
  marked : IsConj (short 1) markedInvolution

/-- Testing on all single-coordinate vectors suffices for an additive
intertwiner. No scalar structure on the target beyond its actual binary one
is needed. -/
theorem equivariant_of_single (c : Six F →+ LeechModTwo)
    (g : LeechCentralQuotient) (a : LinearGroup)
    (h : ∀ j b, quotientModTwoRepresentation g (c (Pi.single j b)) =
      c (a (Pi.single j b))) (v : Six F) :
    quotientModTwoRepresentation g (c v) = c (a v) := by
  let left := (quotientModTwoRepresentation g).toAddEquiv.toAddMonoidHom.comp c
  let right := c.comp a.toAddEquiv.toAddMonoidHom
  have he : left = right := AddMonoidHom.functions_ext _ _ _ h
  exact DFunLike.congr_fun he v

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
