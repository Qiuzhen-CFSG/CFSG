module
public import Theory.GroupTheory.Commutator.BoundedImageKernel

/-!
# A moving subgroup supplements the common fixed subgroup

Let an abelian ambient subgroup A have its commutators with T in a line Z
of order two contained in A. Suppose an index-two subgroup Q of T centralizes
A. Any subgroup B≤A with nontrivial T-commutator then supplements the common
fixed subgroup: A=B C_A(T). The conclusion is expressed as a subgroup join.
No additional normality hypothesis on Q, A, or B is needed.

The existing bounded-image kernel theorem supplies a T-fixed subgroup of A
with index at most two. Thus C_A(T) also has index at most two. Since B is
not centralized by T, it escapes C_A(T); the latter has index exactly two.
The relative-index tower then forces their join to equal A. The imported
kernel argument uses the commutator homomorphism for one actor outside Q.

This source-neutral decomposition is used in the central branch of
Stellmacher (9.4), Journal of Algebra190 (1997), with the literal supplied
enlargement, center line, and intersecting local cores.
-/

namespace Subgroup

public theorem sup_inf_centralizer_eq_of_index_two_line_action
    {G : Type*} [Group G] [Finite G]
    (A B Z T Q : Subgroup G) [IsMulCommutative A]
    (hBA : B ≤ A) (hZA : Z ≤ A) (hZcard : Nat.card Z = 2)
    (hcomm : ⁅A,T⁆ ≤ Z) (hQT : Q ≤ T) (hindex : Q.relIndex T = 2)
    (hcentral : ⁅A,Q⁆ = ⊥) (hactive : ⁅B,T⁆ ≠ ⊥) :
    A = B ⊔ (A ⊓ centralizer (T : Set G)) := by
  let C := A ⊓ centralizer (T : Set G)
  have hQC : Q ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcentral)
  obtain ⟨K,hKA,hcard,hKT⟩ := exists_large_subgroup_commutator_le_of_index_two
    A A T Q ⊥ Z le_rfl inferInstance hZA hcomm hQT hQC hindex
  have hKC : K ≤ C := le_inf hKA
    (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hKT))
  rw [relIndex_bot_left,hZcard] at hcard
  have hbound : Nat.card A ≤ 2 * Nat.card C :=
    hcard.trans (Nat.mul_le_mul_left 2 (card_le_of_le hKC))
  have hnot : ¬ B ≤ C := by
    intro hle
    exact hactive (commutator_eq_bot_iff_le_centralizer.mpr (hle.trans inf_le_right))
  have hCindex : C.relIndex A = 2 := by
    have hprod := (C.subgroupOf A).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv] at hprod
    change C.relIndex A * Nat.card C = Nat.card A at hprod
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hle : C.relIndex A ≤ 2 := by nlinarith
    have hne : C.relIndex A ≠ 1 := fun heq =>
      hnot (hBA.trans (relIndex_eq_one.mp heq))
    have hnonzero : C.relIndex A ≠ 0 := (C.subgroupOf A).index_ne_zero_of_finite
    omega
  have hJA : B ⊔ C ≤ A := sup_le hBA inf_le_left
  have htower := relIndex_mul_relIndex C (B ⊔ C) A le_sup_right hJA
  rw [hCindex] at htower
  have hdvd : C.relIndex (B ⊔ C) ∣ 2 := ⟨_,htower.symm⟩
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with hone | htwo
  · exact (hnot (le_sup_left.trans (relIndex_eq_one.mp hone))).elim
  · rw [htwo] at htower
    have hone : (B ⊔ C).relIndex A = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp hone) hJA

end Subgroup
