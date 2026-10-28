module

public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Maximal elementary subgroups from a fixed-point index bound

Let `E ≤ Q ≤ S`, with `E` elementary abelian and central in `Q`.
For a maximum-order elementary subgroup `A` of `S`, a lower bound
`|A : A ∩ Q| ≤ |E : C_E(A)|` forces `(A ∩ Q)E` to have at least
`|A|` elements. It is elementary and lies in `Q`, so maximality gives
another member of the maximum family of `S`.

The proof uses the subgroup-product cardinal formula and cancels the
positive order of `A ∩ E`. The actual Campbell application takes
`Q = O₂(G)` and `E = Ω₁(Z(Q))`.

Source: Neville Ray Campbell, *Pushing up in Finite Groups* (1979),
Chapter II, Lemma 4.1(iv–v), printed p.25,
https://thesis.caltech.edu/17847/.
-/

public section

namespace Stellmacher
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_inf_mul_relIndex (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) * H.relIndex K = Nat.card K := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ K) K bot_le inf_le_right

/-- If the fixed-point index on a central elementary subgroup dominates the
index of a maximum elementary subgroup modulo `Q`, its replacement in `Q`
is still of maximum elementary order in `S`. No normality of `Q` is needed. -/
theorem maxElementary_inf_sup_mem_of_fixedIndex (S Q A E : Subgroup G)
    (hQS : Q ≤ S) (hEQ : E ≤ Q) [IsElementaryAbelian 2 E]
    (hEC : E ≤ Subgroup.centralizer (Q : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hb : Q.relIndex A ≤ (Subgroup.centralizer (A : Set G)).relIndex E) :
    (A ⊓ Q) ⊔ E ∈ elementaryAbelianMaxSubgroups S := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ Q : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hEAC : E ≤ Subgroup.centralizer (A ⊓ Q : Set G) :=
    hEC.trans (Subgroup.centralizer_le inf_le_right)
  have he : IsElementaryAbelian 2 ((A ⊓ Q) ⊔ E : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hEAC
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (A ⊓ Q) E (hEAC.trans (Subgroup.centralizer_le_normalizer _))
  have hAI : (A ⊓ Q) ⊓ E = A ⊓ E := by
    rw [inf_assoc, inf_eq_right.mpr hEQ]
  rw [hAI] at hprod
  have hidx : Q.relIndex A ≤ A.relIndex E := hb.trans
    (Subgroup.relIndex_le_of_le_left
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
      (by
        have hc := card_inf_mul_relIndex A E
        intro hz
        rw [hz, mul_zero] at hc
        exact Nat.card_pos.ne' hc.symm))
  have hAE := card_inf_mul_relIndex A E
  have hQA : Nat.card (A ⊓ Q : Subgroup G) * Q.relIndex A = Nat.card A := by
    simpa only [inf_comm Q A] using card_inf_mul_relIndex Q A
  have hsize : Nat.card A ≤ Nat.card ((A ⊓ Q) ⊔ E : Subgroup G) := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card (A ⊓ E : Subgroup G)) _ Nat.card_pos
    calc
      Nat.card (A ⊓ E : Subgroup G) * Nat.card A =
          Nat.card (A ⊓ Q : Subgroup G) *
            (Nat.card (A ⊓ E : Subgroup G) * Q.relIndex A) := by rw [← hQA]; ac_rfl
      _ ≤ Nat.card (A ⊓ Q : Subgroup G) *
            (Nat.card (A ⊓ E : Subgroup G) * A.relIndex E) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hidx)
      _ = Nat.card (A ⊓ Q : Subgroup G) * Nat.card E := by rw [hAE]
      _ = _ := hprod
  exact ⟨sup_le (inf_le_right.trans hQS) (hEQ.trans hQS), he,
    fun B hBS hBe => (hA.2.2 B hBS hBe).trans hsize⟩


end Stellmacher

end
