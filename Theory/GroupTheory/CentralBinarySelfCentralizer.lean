module
public import Theory.GroupTheory.CentralBinaryCommutatorDuality

/-!
# Orders of binary self-centralizing subgroups

Central binary commutator duality equates the two relative centralizer
indices. For a self-centralizing elementary abelian subgroup U this yields
|U|² = |G| |Z(G)|. In particular, a core of order512 with such a subgroup
of order32 has center of order two. The same duality shows that every
abelian subgroup has order at most |U|: enlarge it by the central target,
then compare its intersection with U to its centralizer in U.

The proof takes cardinalities in the actual duality isomorphism from F.9.7
of Aschbacher--Smith (combined manuscript, printed p.321). It does not
assume nondegeneracy or equality of the centralizer indices.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Central binary duality equates the literal relative centralizer indices. -/
theorem centralizer_relIndex_eq_of_central_binary_commutators
    (Q U Z : Subgroup G) [IsElementaryAbelian 2 U]
    [(centralizer (U : Set G)).subgroupOf Q |>.Normal]
    (hZQ : Z ≤ Q) (hZ : Z ≤ center G) (hcomm : ⁅Q,U⁆ ≤ Z)
    (hcard : Nat.card Z = 2) :
    (centralizer (U : Set G)).relIndex Q =
      (centralizer (Q : Set G)).relIndex U := by
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard (by simp)
  obtain ⟨e,_⟩ := exists_central_binary_commutator_duality Q U Z hZQ hZ hcomm eZ
  change Nat.card (Q ⧸ (centralizer (U : Set G)).subgroupOf Q) =
    Nat.card (U ⧸ (centralizer (Q : Set G)).subgroupOf U)
  exact (Nat.card_congr e.toEquiv).trans MonoidHom.binary_dual_card

/-- The order identity for an elementary abelian self-centralizer. -/
theorem card_sq_eq_card_mul_center_of_central_binary_selfCentralizer
    (U Z : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZ : Z ≤ center G) (hcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G),U⁆ ≤ Z)
    (hcentralizer : centralizer (U : Set G) = U) :
    Nat.card U * Nat.card U = Nat.card G * Nat.card (center G) := by
  have hcU : center G ≤ U := by
    rw [← hcentralizer]
    intro c hc u _
    exact mem_center_iff.mp hc u
  have hi := centralizer_relIndex_eq_of_central_binary_commutators ⊤ U Z
    le_top hZ hcomm hcard
  have hCtop : centralizer ((⊤ : Subgroup G) : Set G) = center G := by
    exact centralizer_univ
  rw [hcentralizer, hCtop, relIndex_top_right] at hi
  have hU := U.index_mul_card
  have hC := ((center G).subgroupOf U).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hcU).toEquiv] at hC
  change (center G).relIndex U * Nat.card (center G) = Nat.card U at hC
  rw [← hi] at hC
  calc
    Nat.card U * Nat.card U =
        (U.index * Nat.card (center G)) * Nat.card U := by rw [hC]
    _ = (U.index * Nat.card U) * Nat.card (center G) := by ring
    _ = _ := by rw [hU]

/-- An elementary self-centralizer with binary central commutators has maximum abelian order. -/
theorem card_abelian_le_of_central_binary_selfCentralizer
    (U Z A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [IsMulCommutative A]
    (hZ : Z ≤ center G) (hcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G),U⁆ ≤ Z)
    (hcentralizer : centralizer (U : Set G) = U) :
    Nat.card A ≤ Nat.card U := by
  let B := A ⊔ Z
  have hBA : B ≤ centralizer (A : Set G) :=
    sup_le (le_centralizer A) (hZ.trans (center_le_centralizer _))
  have hBB : B ≤ centralizer (B : Set G) :=
    sup_le (le_centralizer_iff.mp hBA) (hZ.trans (center_le_centralizer _))
  let : IsMulCommutative B := le_centralizer_iff_isMulCommutative.mp hBB
  have hi := centralizer_relIndex_eq_of_central_binary_commutators B U Z
    le_sup_right hZ ((commutator_mono le_top le_rfl).trans hcomm) hcard
  rw [hcentralizer] at hi
  have hkcard : Nat.card (U.subgroupOf B) ≤
      Nat.card ((centralizer (B : Set G)).subgroupOf U) := by
    rw [← inf_subgroupOf_left,
      Nat.card_congr (subgroupOfEquivOfLe (show B ⊓ U ≤ B from inf_le_left)).toEquiv]
    rw [← inf_subgroupOf_left,
      Nat.card_congr (subgroupOfEquivOfLe
        (show U ⊓ centralizer (B : Set G) ≤ U from inf_le_left)).toEquiv]
    exact card_le_of_le (le_inf inf_le_right (inf_le_left.trans hBB))
  have hB := (U.subgroupOf B).index_mul_card
  have hU := ((centralizer (B : Set G)).subgroupOf U).index_mul_card
  change U.relIndex B * Nat.card (U.subgroupOf B) = Nat.card B at hB
  change (centralizer (B : Set G)).relIndex U *
    Nat.card ((centralizer (B : Set G)).subgroupOf U) = Nat.card U at hU
  rw [hi] at hB
  apply (card_le_of_le (show A ≤ B from le_sup_left)).trans
  rw [←hB,←hU]
  exact Nat.mul_le_mul_left _ hkcard

end Subgroup
