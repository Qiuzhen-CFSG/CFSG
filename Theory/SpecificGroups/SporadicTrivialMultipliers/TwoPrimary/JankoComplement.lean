module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoComplement.Construction

/-!
# Invariant complements in elementary lifts of the J4 Mathieu core

Every central double extension of the literal ATLAS max1 subgroup whose core
preimage has exponent two admits a normal complement to its central kernel
inside that preimage. Choose twelve binary coordinates with the central line
last, use five quotient relators to correct the lower coordinate to an
invariant functional, and take its kernel.

This proves the independent conditional `InvariantComplementCalculation`
contract. The final theorem applies it to the original `localProjection` of a
perfect central cover, retaining the same elementary-preimage hypothesis.

Source: Aschbacher–Smith I.1.1–I.1.5, printed pp.407–408, and GLS3 Section 6.1;
the concrete action is certified from the ATLAS `J4G1-max1W1` coordinates.
-/

public section
namespace Janko4.TwoPrimary
open Subgroup InvariantComplement
universe u

/-- Every central double extension of the literal J4 max1 local group whose
core preimage has exponent two has an invariant complement to its central line. -/
theorem invariantComplementCalculation : InvariantComplementCalculation.{u} := by
  intro L _ _ q hq hc hk he
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : q.ker)).mp hk
  obtain ⟨a, ha⟩ := hq x
  obtain ⟨b, hb⟩ := hq y
  obtain ⟨c⟩ := exists_preCoordinates q hq hk he z hz
  obtain ⟨d, ⟨c'⟩⟩ := exists_liftCoordinates q hc a b ha hb z c
  exact normal_complement_of_coordinates q hq hc hk he z hz a b ha hb d c'

/-- The invariant complement for the original restricted perfect covering map,
assuming precisely the independent elementary-preimage calculation. -/
theorem localProjection_invariant_complement
    {E : Type*} [Group E] [Finite E] (f : PerfectCentralCovering.Cover E Model)
    (hk : Nat.card f.toMonoidHom.ker = 2) (he : ElementaryPreimage (localProjection f)) :
    ∃ T : Subgroup (Local.comap f.toMonoidHom), T.Normal ∧
      Disjoint (localProjection f).ker T ∧ T.map (localProjection f) = Core := by
  apply invariantComplementCalculation _ (localProjection f)
  · exact f.toMonoidHom.subgroupComap_surjective_of_surjective Local f.surjective
  · intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (f.ker_le_center (congrArg Subtype.val hx)) y)
  · exact (localProjection_kernel_card f).trans hk
  · exact he

end Janko4.TwoPrimary
