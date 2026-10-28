module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames

/-!
# The scalar fixed-space witness supplied by the long frame

The six coordinates over GF(4) give twelve binary dimensions in the literal
U-fixed space. The existing scalar lift theorem gives a negative-square lift
of any nonidentity member of U; its fixed space also has dimension twelve.
Containment therefore gives equality, supplying exactly the scalar input to
the positive-square kernel reduction. Construction of the long frame stays
with its existing owner.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283, where the
natural-plus-dual SL₃(4) module supplies this dimension equality.
-/

public section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare
open LocalGenerators OctonionLocals

/-- The actual long-frame coordinates discharge the scalar fixed-space input. -/
theorem scalarFixedSpaceWitness_of_longFrame (L : LongFrame) : ScalarFixedSpaceWitness := by
  have hm (w : Six F) : L.coordinates w ∈ fixedSpace :=
    (L.coordinates_range _).mpr ⟨w, rfl⟩
  let f : Six F → fixedSpace := fun w => ⟨L.coordinates w, hm w⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact L.coordinates_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨w, hw⟩ := (L.coordinates_range v.val).mp v.property
      exact ⟨w, Subtype.ext hw⟩
  have hcard : Nat.card fixedSpace = 2 ^ 12 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
      GaloisField.card 2 2 (by decide)]
    norm_num
  have hdim : Module.finrank Bit fixedSpace = 12 := by
    rw [Module.natCard_eq_pow_finrank (K := Bit), Nat.card_zmod] at hcard
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hcard
  have hn : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [U_card]; decide)
  obtain ⟨u, hu⟩ := exists_ne (1 : U)
  have hune : u.val ≠ 1 := fun he => hu (Subtype.ext he)
  obtain ⟨a, ha, hasq⟩ := U_involution_lift u hune
  have hle : fixedSpace ≤ LinearMap.ker (difference u.val) := by
    intro v hv
    rw [LinearMap.mem_ker]
    change quotientModTwoRepresentation u.val v - v = 0
    rw [hv u.val u.property, sub_self]
  have heq : fixedSpace = LinearMap.ker (difference u.val) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hdim, U_involution_fixed_finrank u hune]
  refine ⟨a, hasq, ha ▸ u.property, ?_⟩
  intro v hv
  rw [heq, LinearMap.mem_ker]
  change quotientModTwoRepresentation u.val v - v = 0
  rw [← ha, quotientModTwoRepresentation_compatible, hv, sub_self]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare
