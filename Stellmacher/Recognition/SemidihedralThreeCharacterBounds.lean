module

public import Stellmacher.Recognition.SemidihedralThreeCharacterOrderBounds
public import Stellmacher.Recognition.SemidihedralThreeCyclicBlocks

/-!
# Semidihedral characteristic-three character bounds

For an involution `x` in a finite simple semidihedral N₂-group, write `N`
for its centralizer, `K` for the mapped odd core, and `A = C_G(T) ∩ K` for
an elementary four-group `T` containing `x`. Put `a = |A|` and `b = [K:A]`.

The actual principal characters supply the local Schur divisor and the two
global order alternatives. The cyclic-block conclusions give their residues
modulo eleven and thirteen and the exact three-part in the second case.
Combining these with `|N| = 48ab` proves the bounds used by odd-core elimination.
All character witnesses are constructed from the original group hypotheses.
The numerical helpers remain publicly re-exported from their base module.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 1, Lemmas 1--4,
and Proposition 5, especially article pp.111 and 114--117.
-/

namespace Stellmacher.Recognition

/-- The ABG characteristic-three bounds for the actual odd-core parameters,
with no additional character-theoretic or core-freeness hypotheses. -/
public theorem semidihedral_three_character_bounds
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    let a := Nat.card A
    let b := A.index
    b ≠ 1 → a * b ∣ 15 ∧
      ((a * b^3 ∣ 3^4 * 5 ∧ a * b^3 % 11 = 1) ∨
        (Nat.Coprime (a * b) 3 ∧ a * b^3 % 13 = 1)) := by
  exact semidihedral_three_character_bounds_of_order_data S hS hN x hx T
    (semidihedral_three_cyclic_blocks S hS hN x hx T hT hxT)

end Stellmacher.Recognition
