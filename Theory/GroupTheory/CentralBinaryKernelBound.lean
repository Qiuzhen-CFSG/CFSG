module
public import Theory.GroupTheory.CentralBinarySelfCentralizer

/-!
# Bounding a group by its binary commutator kernel

If an elementary normal subgroup U satisfies [G,U] ≤ Z for a central
subgroup Z of order two contained in U, commutator duality gives
|G| |C_U(G)| = |U| |C_G(U)|. Consequently 2|G| ≤ |C_G(U)|².
Unlike the self-centralizing case, this bounds the whole group using the
order of the actual action kernel without assuming that kernel equals U.

The source application bounds the original quintic core from its
radius-two ball kernel. Source: Aschbacher--Smith F.9.7, printed p.321.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The orders of both radicals give the exact commutator-pairing identity. -/
theorem card_mul_fixed_eq_card_mul_centralizer_of_central_binary_commutators
    (U Z : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZ : Z ≤ center G) (hcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G), U⁆ ≤ Z) :
    Nat.card G * Nat.card (U ⊓ center G : Subgroup G) =
      Nat.card U * Nat.card (centralizer (U : Set G)) := by
  have hi := centralizer_relIndex_eq_of_central_binary_commutators ⊤ U Z
    le_top hZ hcomm hcard
  have htop : centralizer ((⊤ : Subgroup G) : Set G) = center G := centralizer_univ
  rw [htop, relIndex_top_right] at hi
  have hc := (centralizer (U : Set G)).index_mul_card
  have hu := ((center G).subgroupOf U).index_mul_card
  rw [← inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe
    (show U ⊓ center G ≤ U from inf_le_left)).toEquiv] at hu
  change (U ⊓ center G).relIndex U * Nat.card (U ⊓ center G : Subgroup G) =
    Nat.card U at hu
  rw [inf_relIndex_left, ← hi] at hu
  calc
    Nat.card G * Nat.card (U ⊓ center G : Subgroup G) =
        ((centralizer (U : Set G)).index * Nat.card (centralizer (U : Set G))) *
          Nat.card (U ⊓ center G : Subgroup G) := by rw [hc]
    _ = ((centralizer (U : Set G)).index *
        Nat.card (U ⊓ center G : Subgroup G)) * Nat.card (centralizer (U : Set G)) := by ring
    _ = _ := by rw [hu]

/-- The central target lies in the right radical and supplies its factor two. -/
theorem twice_card_le_card_mul_centralizer_of_central_binary_commutators
    (U Z : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hZ : Z ≤ center G) (hcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G), U⁆ ≤ Z) :
    2 * Nat.card G ≤ Nat.card U * Nat.card (centralizer (U : Set G)) := by
  have hrad : 2 ≤ Nat.card (U ⊓ center G : Subgroup G) := by
    rw [← hcard]
    exact card_le_of_le (le_inf hZU hZ)
  rw [← card_mul_fixed_eq_card_mul_centralizer_of_central_binary_commutators
    U Z hZ hcard hcomm]
  nlinarith

/-- The binary commutator kernel has square order at least twice the ambient order. -/
theorem twice_card_le_centralizer_card_sq_of_central_binary_commutators
    (U Z : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hZ : Z ≤ center G) (hcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G), U⁆ ≤ Z) :
    2 * Nat.card G ≤ Nat.card (centralizer (U : Set G)) ^ 2 := by
  have hU := card_le_of_le (le_centralizer U)
  have hh := twice_card_le_card_mul_centralizer_of_central_binary_commutators
    U Z hZU hZ hcard hcomm
  nlinarith

end Subgroup
