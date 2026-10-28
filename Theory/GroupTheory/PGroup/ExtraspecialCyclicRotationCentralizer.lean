module

public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# Centralizers in an extraspecial rotation product

Let an extraspecial eight commute with cyclic rotations. Suppose an outside
involution acts on the extraspecial factor by an inner automorphism, inverts
an order-four rotation whose square lies in the factor, and fixes exactly two
rotations. Multiplying factor elements by this order-four rotation when needed
corrects their commutators with the involution.

The corrected centralizer and the rotations generate the rotation product.
Their intersection has order two, so the product formula gives centralizer
order eight. An abelian centralizer would make the extraspecial factor abelian;
hence this centralizer is extraspecial. An outside involution then doubles its
order in the full centralizer.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392, Case 1.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Subgroup

private theorem correction_in_rotation_product
    {P : Type*} [Group P] [Finite P]
    (A R : Subgroup P) [IsExtraspecial 2 A]
    (hc : R ≤ centralizer (A : Set P))
    (t w : P) (hwR : w ∈ R) (hw : orderOf w = 4) (hwA : w ^ 2 ∈ A)
    (hwi : t * w * t⁻¹ = w⁻¹)
    (hinner : ∃ a ∈ A, ∀ b ∈ A, t * b * t⁻¹ = a * b * a⁻¹) :
    ∀ b ∈ A, ∃ r ∈ R, b * r ∈ (A ⊔ R) ⊓ centralizer ({t} : Set P) := by
  obtain ⟨a, ha, hinner⟩ := hinner
  have hwZ : (⟨w ^ 2, hwA⟩ : A) ∈ center A := mem_center_iff.mpr (by
    intro b
    exact Subtype.ext (hc (R.pow_mem hwR 2) b b.property))
  have hwne : w ^ 2 ≠ 1 := by
    intro h
    have hh := orderOf_dvd_of_pow_eq_one h
    rw [hw] at hh
    norm_num at hh
  intro b hb
  let aA : A := ⟨a, ha⟩
  let bA : A := ⟨b, hb⟩
  have hz : ⁅aA, bA⁆ ∈ center A :=
    (IsExtraspecial.quotient_elementary_abelian 2 A).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hcases : ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = w ^ 2 := by
    by_cases h : ⁅a, b⁆ = 1
    · exact Or.inl h
    · right
      obtain ⟨z, _, he⟩ := (Nat.card_eq_two_iff' (1 : center A)).mp
        (IsExtraspecial.center_order_p 2 A)
      have hh := (he ⟨⁅aA, bA⁆, hz⟩ (by
        intro h'
        exact h (congrArg (fun x : center A => ((x : A) : P)) h'))).trans
        (he ⟨⟨w ^ 2, hwA⟩, hwZ⟩ (by
          intro h'
          exact hwne (congrArg (fun x : center A => ((x : A) : P)) h'))).symm
      exact congrArg (fun x : center A => ((x : A) : P)) hh
  rcases hcases with h | h
  · refine ⟨1, R.one_mem, ?_, ?_⟩
    · simpa using (mem_sup_left hb : b ∈ A ⊔ R)
    · apply mem_centralizer_singleton_iff.mpr
      have he : t * b * t⁻¹ = b := by
        rw [hinner b hb]
        have hh := congrArg (fun x : P => x * b) h
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one, one_mul] using hh
      simpa using (mul_inv_eq_iff_eq_mul.mp he).symm
  · refine ⟨w, hwR, mul_mem_sup hb hwR, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have hbconj : t * b * t⁻¹ = w ^ 2 * b := by
      rw [hinner b hb]
      have hh := congrArg (fun x : P => x * b) h
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    have he : t * (b * w) * t⁻¹ = b * w := by
      calc
        t * (b * w) * t⁻¹ = (t * b * t⁻¹) * (t * w * t⁻¹) := by group
        _ = (w ^ 2 * b) * w⁻¹ := by rw [hbconj, hwi]
        _ = (b * w ^ 2) * w⁻¹ := by rw [← hc (R.pow_mem hwR 2) b hb]
        _ = b * w := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- An inverted cyclic four corrects an inner action on an extraspecial eight. -/
public theorem extraspecial_eight_centralizer_of_rotation_data
    {P : Type*} [Group P] [Finite P]
    (A R : Subgroup P) [R.Normal] [IsCyclic R] [IsExtraspecial 2 A]
    (hA : Nat.card A = 8)
    (hc : R ≤ centralizer (A : Set P))
    (hM : Nat.card (A ⊔ R : Subgroup P) = 4 * Nat.card R)
    (hi : (A ⊔ R).index = 2)
    (t : P) (ht : t ^ 2 = 1) (hout : t ∉ A ⊔ R)
    (hinner : ∃ a ∈ A, ∀ b ∈ A, t * b * t⁻¹ = a * b * a⁻¹)
    (hfix : Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) = 2)
    (w : P) (hwR : w ∈ R) (hw : orderOf w = 4) (hwA : w ^ 2 ∈ A)
    (hwi : t * w * t⁻¹ = w⁻¹) :
    IsExtraspecial 2 ((A ⊔ R) ⊓ centralizer ({t} : Set P) : Subgroup P) ∧
      Nat.card ((A ⊔ R) ⊓ centralizer ({t} : Set P) : Subgroup P) = 8 ∧
      Nat.card (centralizer ({t} : Set P)) = 16 := by
  let M := A ⊔ R
  let C := centralizer ({t} : Set P)
  let J := M ⊓ C
  have hJR : J ⊔ R = M := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    apply sup_le _ le_sup_right
    intro b hb
    obtain ⟨r, hr, hbr⟩ := correction_in_rotation_product A R hc t w hwR hw hwA hwi hinner b hb
    have hh := (J ⊔ R).mul_mem (mem_sup_left hbr) (inv_mem (mem_sup_right hr))
    simpa only [mul_inv_cancel_right] using hh
  have hRc : R ≤ centralizer (M : Set P) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp hc) R.le_centralizer
  have hIJ : J ⊓ R = R ⊓ C := by
    apply le_antisymm
    · exact fun _ h => ⟨h.2, h.1.2⟩
    · exact fun _ h => ⟨⟨mem_sup_right h.1, h.2⟩, h.1⟩
  have hJ : Nat.card J = 8 := by
    have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes J R
      ((hRc.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _))
    rw [hIJ, hfix, hJR, hM] at he
    have hp : 0 < Nat.card R := Nat.card_pos
    nlinarith
  have hn : ¬ IsMulCommutative J := by
    intro hh
    let : IsMulCommutative J := hh
    have hJJ : J ≤ centralizer (J : Set P) := J.le_centralizer
    have hRJ : R ≤ centralizer (J : Set P) := hRc.trans (centralizer_le inf_le_left)
    have hMM : M ≤ centralizer (M : Set P) := by
      have hMJ : M ≤ centralizer (J : Set P) := hJR ▸ sup_le hJJ hRJ
      have hs : J ⊔ R ≤ centralizer (M : Set P) := sup_le (le_centralizer_iff.mp hMJ) hRc
      simpa only [hJR] using hs
    have hAA : A ≤ centralizer (A : Set P) :=
      (le_sup_left.trans hMM).trans (centralizer_le (show (A : Set P) ⊆ M from fun _ hx => (show A ≤ M from le_sup_left) hx))
    have hZ : center A = ⊤ := by
      apply eq_top_iff.mpr
      intro a _
      exact mem_center_iff.mpr (fun b => Subtype.ext (hAA a.property b b.property))
    have hzcard := IsExtraspecial.center_order_p 2 A
    rw [hZ, card_top, hA] at hzcard
    norm_num at hzcard
  have hC : C = J ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      by_cases hxm : x ∈ M
      · exact mem_sup_left ⟨hxm, hx⟩
      · have hxtM : x * t⁻¹ ∈ M := (mul_mem_iff_of_index_two hi).mpr (by
          simpa only [inv_mem_iff] using iff_of_false hxm hout)
        have htC : t ∈ C := mem_centralizer_singleton_iff.mpr (Commute.refl t)
        have hxtJ : x * t⁻¹ ∈ J := ⟨hxtM, C.mul_mem hx (C.inv_mem htC)⟩
        have he := (J ⊔ zpowers t).mul_mem (mem_sup_left hxtJ) (mem_sup_right (mem_zpowers t))
        simpa only [inv_mul_cancel_right] using he
    · exact sup_le inf_le_right (zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (Commute.refl t)))
  have hcardC : Nat.card C = 16 := by
    rw [hC, card_sup_zpowers_of_normalizing_involution J t ht (fun h => hout h.1) ?_, hJ]
    apply centralizer_le_normalizer
    intro j hj
    exact (mem_centralizer_singleton_iff.mp hj.2)
  exact ⟨IsExtraspecial.of_noncommutative_card_eight hJ hn, hJ, hcardC⟩
end Subgroup
