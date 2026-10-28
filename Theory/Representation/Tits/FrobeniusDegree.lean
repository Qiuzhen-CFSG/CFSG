module

public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.SpecificGroups.Tits.FiveFrobenius

/-!
# A degree bound from the actual Tits five-local subgroup

The certified abelian subgroup of order 25 has a fixed-point-free normalizing
subgroup of order 24. The orbit of a nontrivial weight therefore forces degree
at least 24 for every faithful characteristic-two representation. The general
scalar-extension theorem permits arbitrary coefficient fields and does not
require irreducibility.

Source: the ATLAS Tits word program TF42G1-max8W1, certified in FiveFrobenius;
the weight-orbit argument used in Aschbacher–Smith G.7.2(2), pp.347–348.
-/

public section
namespace Representation.TitsFrobeniusDegree

/-- Every faithful characteristic-two representation of the genuine Tits
carrier has degree at least twenty-four. -/
theorem finrank_ge_twenty_four
    {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F Tits.ParrottGroup V) (hρ : Function.Injective ρ) :
    24 ≤ Module.finrank F V := by
  let : Nontrivial Tits.fiveKernel :=
    (Finite.one_lt_card_iff_nontrivial (α := Tits.fiveKernel)).mp
      (by rw [Tits.fiveKernel_card]; decide)
  have horder : (Nat.card Tits.fiveKernel : F) ≠ 0 :=
    (CharP.cast_eq_zero_iff F 2 (Nat.card Tits.fiveKernel)).not.mpr
      (by rw [Tits.fiveKernel_card]; decide)
  simpa only [Tits.fiveComplement_card] using
    card_le_finrank_of_fixedPointFree_normalizer_of_field ρ
      Tits.fiveKernel Tits.fiveComplement hρ horder
      Tits.fiveComplement_normalizes Tits.fiveComplement_free

end Representation.TitsFrobeniusDegree
