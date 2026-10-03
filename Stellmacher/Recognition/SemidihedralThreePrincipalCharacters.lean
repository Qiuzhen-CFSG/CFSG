module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Stellmacher.Recognition.SemidihedralThreePrincipalData
public import Stellmacher.Recognition.SemidihedralThreePrincipalConstruction
public import Stellmacher.Recognition.SemidihedralThreePrincipalOrderIdentity

/-!
# Assembly of the characteristic-three principal-block data

The character package retains a bijection with the actual principal block,
the four rational characters, all three exceptional characters, and their
two-singular restrictions. The principal-block construction supplies these
characters under the simple semidihedral N₂ hypotheses. The ABG
involution-pair order identity then gives the two degree and order alternatives
arithmetically.

This assembles the principal-block construction in III.5--6 and the order
identity in III.7. The local quotient theorem supplies GL₂(3) modulo the odd
core, without eliminating it.

Source: Alperin--Brauer--Gorenstein, III.2 Proposition 6 and III.8
Proposition 1, article pp.68--69 and 111.
-/

namespace Stellmacher.Recognition
open ABG

/-- The full characteristic-three principal-block package exists for every
involution and four-group containing it in a simple semidihedral N₂-group.
Its rows are the actual distinct irreducible characters of the principal
two-block, including the principal row and all three exceptional rows. -/
public theorem exists_semidihedralThreePrincipalCharacters
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    Nonempty (SemidihedralThreePrincipalCharacters G x T) := by
  obtain ⟨c⟩ := exists_threePrincipalData S hS hN x hx
  exact ⟨{ toThreePrincipalData := c
           order_identity := semidihedral_threePrincipal_order_identity S hS hN x hx T hT hxT c }⟩

/-- The two group-order alternatives of ABG III.8 Proposition 1, with the
actual odd-core intersection and its index as parameters. -/
public theorem semidihedral_three_principal_order_alternatives
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let A := threePrincipalCoreCentralizer x T
    Nat.card G = 7920 * (Nat.card A * A.index^3) ∨
      Nat.card G = 5616 * (Nat.card A * A.index^3) := by
  obtain ⟨c⟩ := exists_semidihedralThreePrincipalCharacters S hS hN x hx T hT hxT
  rcases c.alternatives with h | h
  · exact Or.inl h.2.2.2.2.2
  · exact Or.inr h.2.2.2.2.2

end Stellmacher.Recognition
