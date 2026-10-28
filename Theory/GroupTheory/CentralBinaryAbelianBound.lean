module
public import Theory.GroupTheory.CentralBinaryCentralizerCard
public import Mathlib.GroupTheory.Index

/-!
# Abelian subgroups and a binary commutator kernel

Let U be normal abelian with [U,G] contained in a central subgroup Z
of order two inside U. Every abelian subgroup A has order at most
|C_G(U)|. Indeed, binary commutator duality identifies
|U| |C_A(U)| with |A| |C_U(A)|. The subgroup U C_A(U) lies in C_G(U),
and A∩U lies in C_U(A), giving the bound by cancellation.

No bound on [G,G], the order of G or its full center is assumed. The
original quintic application proves that every cubic conjugate
intersection of O₂(H) is nonabelian. Source: the binary commutator
pairing of Aschbacher--Smith F.9.7, printed p.321.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Every abelian subgroup is bounded by the centralizer of a normal
abelian subgroup whose commutators lie in a central subgroup of order two. -/
theorem card_abelian_le_centralizer_of_central_binary_commutators
    (U A Z : Subgroup G) [U.Normal] [IsMulCommutative U] [IsMulCommutative A]
    (hZU : Z ≤ U) (hZ : Z ≤ center G) (hz : Nat.card Z = 2)
    (hc : ⁅U, ⊤⁆ ≤ Z) :
    Nat.card A ≤ Nat.card (centralizer (U : Set G)) := by
  let C := centralizer (U : Set G)
  let D := A ⊓ C
  let R := U ⊓ centralizer (A : Set G)
  let W := U ⊔ D
  let : IsMulCommutative Z := le_centralizer_iff_isMulCommutative.mp
    (hZ.trans (center_le_centralizer _))
  have hpair := card_mul_card_centralizer_restrict_of_central_binary_pairing
    U A Z hZU ((commutator_mono le_rfl le_top).trans hc)
    (by rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]; exact hZ.trans (center_le_centralizer _)) hz
  rw [← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ C ≤ A from inf_le_left)).toEquiv,
    ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe (show R ≤ U from inf_le_left)).toEquiv] at hpair
  change Nat.card U * Nat.card D = Nat.card A * Nat.card R at hpair
  have hW : W ≤ C := sup_le (le_centralizer U) inf_le_right
  have hI : D ⊓ U ≤ R := le_inf inf_le_right
    ((inf_le_left.trans inf_le_left).trans (le_centralizer A))
  have hWcard := (U.subgroupOf W).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show U ≤ W from le_sup_left)).toEquiv] at hWcard
  change U.relIndex W * Nat.card U = Nat.card W at hWcard
  have hDcard := (U.subgroupOf D).index_mul_card
  rw [← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe (show D ⊓ U ≤ D from inf_le_left)).toEquiv] at hDcard
  change (D ⊓ U).relIndex D * Nat.card (D ⊓ U : Subgroup G) = Nat.card D at hDcard
  rw [inf_relIndex_left] at hDcard
  have hidx : U.relIndex W = U.relIndex D := relIndex_sup_left D U
  have hprod : Nat.card U * Nat.card D = Nat.card W * Nat.card (D ⊓ U : Subgroup G) := by
    rw [←hWcard, hidx, ←hDcard]
    ring
  have hh : Nat.card A * Nat.card R ≤ Nat.card C * Nat.card R := by
    rw [←hpair, hprod]
    exact Nat.mul_le_mul (card_le_of_le hW) (card_le_of_le hI)
  exact Nat.le_of_mul_le_mul_right hh Nat.card_pos

end Subgroup
