module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner

/-!
# Words for the Held outer fixed subgroup

For the published involution `action`, the element `twist` is inverted by the
action. Its order divides 21, so the Bray word `bray` is fixed. The two words
`bray²` and `(a * bray)¹²` will give a perfect subgroup of the literal fixed
subgroup. Their fixedness and relations are proved in `Generators`.

Source: the exact ATLAS HeG1-p2058B0 carrier and the outer 2C row of GLS3,
Table 5.3p, interpreted with the perfect-cover convention on pp.260–261.
-/

@[expose] public section

namespace Held.OuterInvolution.FixedStructure

/-- The product of the involution and its conjugate by `b³`, expressed in Held. -/
def twist : He := action ((b ^ 3)⁻¹) * b ^ 3

/-- The odd-order Bray construction for the fixed subgroup. -/
def bray : He := b ^ 3 * twist ^ 10

end Held.OuterInvolution.FixedStructure
