module

public import Theory.GroupTheory.ElementaryThompsonReplacement

/-!
# The upper fixed-index bound for maximum elementary subgroups

If E is elementary abelian and central in Q≤S, replacing A by (A∩Q)E
bounds |E:A∩E| by |A:A∩Q|. The fixed-index |E:C_E(A)| is no larger.
This is the upper half of the sharp index chain in Campbell II.4.1,
*Pushing up in Finite Groups* (1979), printed p.25.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]
theorem maxElementary_fixedIndex_le_relIndex (S Q A E : Subgroup G) (hQS : Q ≤ S)
    (hEQ : E ≤ Q) [IsElementaryAbelian 2 E]
    (hEC : E ≤ centralizer (Q : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    (centralizer (A : Set G)).relIndex E ≤ A.relIndex E ∧
      A.relIndex E ≤ Q.relIndex A := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAC : A ≤ centralizer (A : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  refine ⟨relIndex_le_of_le_left hAC index_ne_zero_of_finite,?_⟩
  let D := (A ⊓ Q) ⊔ E
  let : IsElementaryAbelian 2 (A ⊓ Q : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  have hEAC := hEC.trans (centralizer_le (show A ⊓ Q ≤ Q from inf_le_right))
  have hDe : IsElementaryAbelian 2 D := IsElementaryAbelian.sup_of_le_centralizer hEAC
  have hcard : Nat.card D ≤ Nat.card A := hA.2.2 D
    (sup_le (inf_le_right.trans hQS) (hEQ.trans hQS)) hDe
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes (A ⊓ Q) E
    (hEAC.trans (Subgroup.centralizer_le_normalizer _))
  have hI : (A ⊓ Q) ⊓ E = A ⊓ E := by rw [inf_assoc,inf_eq_right.mpr hEQ]
  rw [hI] at hp
  have hi (X Y : Subgroup G) : Nat.card (X ⊓ Y : Subgroup G) * X.relIndex Y = Nat.card Y := by
    simpa only [relIndex_bot_left,inf_relIndex_right] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (X ⊓ Y) Y bot_le inf_le_right
  have hAE := hi A E
  have hQA : Nat.card (A ⊓ Q : Subgroup G) * Q.relIndex A = Nat.card A := by
    simpa only [inf_comm Q A] using hi Q A
  apply Nat.le_of_mul_le_mul_left (c := Nat.card (A ⊓ E : Subgroup G)) _ Nat.card_pos
  apply Nat.le_of_mul_le_mul_left (c := Nat.card (A ⊓ Q : Subgroup G)) _ Nat.card_pos
  calc
    Nat.card (A ⊓ Q : Subgroup G) * (Nat.card (A ⊓ E : Subgroup G) * A.relIndex E) =
        Nat.card (A ⊓ E : Subgroup G) * Nat.card D := by rw [hAE]; exact hp
    _ ≤ Nat.card (A ⊓ E : Subgroup G) * Nat.card A := Nat.mul_le_mul_left _ hcard
    _ = Nat.card (A ⊓ Q : Subgroup G) * (Nat.card (A ⊓ E : Subgroup G) * Q.relIndex A) := by
      rw [← hQA]; ac_rfl
end Stellmacher
