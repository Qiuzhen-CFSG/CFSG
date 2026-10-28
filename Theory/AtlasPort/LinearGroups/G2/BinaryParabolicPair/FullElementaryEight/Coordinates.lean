module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Levi

/-!
# A small involution-centralizer certificate for the binary first parabolic

The first parabolic is a product of the 32-element root core and its
six-element Levi complement. The common Sylow uses the identity and one
reflection in the Levi factor. For any other Levi factor, at most four
square-one Sylow coordinates commute with a prescribed parabolic coordinate.
The certificate checks these finite coordinate equations, without enumerating
subgroups. This is used for the elementary eights in Aschbacher--Smith,
14.2.21--22 (printed p.988); the root coordinates are from the licensed ATLAS port.
-/

@[expose] public section
namespace Atlas.G2.BinaryParabolicPair.FullElementaryEight
open BinaryCore

def leviAction : DihedralGroup 3 → Coordinates → Coordinates
  | .r i, x => (cubicConjugate^[i.val]) x
  | .sr i, x => shortConjugate ((cubicConjugate^[i.val]) x)

def binaryLevi (b : Bool) : DihedralGroup 3 := if b then .sr 0 else 1

def centralizingInvolutions (n : Coordinates) (l : DihedralGroup 3) :
    Finset (Coordinates × Bool) :=
  Finset.univ.filter fun y =>
    y.1 * leviAction (binaryLevi y.2) y.1 = 1 ∧
    n * leviAction l y.1 = y.1 * leviAction (binaryLevi y.2) n ∧
    l * binaryLevi y.2 = binaryLevi y.2 * l

set_option maxRecDepth 100000 in
theorem centralizingInvolutions_card : ∀ (n : Coordinates) (l : DihedralGroup 3),
    l ≠ 1 → l ≠ .sr 0 → (centralizingInvolutions n l).card ≤ 4 := by
  decide +kernel

end Atlas.G2.BinaryParabolicPair.FullElementaryEight
