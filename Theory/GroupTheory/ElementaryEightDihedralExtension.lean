module

public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.AbelianIndexTwoCenter
public import Theory.ElementaryAbelian.Join

/-!
# The two elementary extensions of a central eight

A central elementary eight, an element of order four whose square lies in
that eight, and an external involution inverting that element generate a
group of order thirty-two. Its center is the original eight, and its only
elementary sixteens are the two literal reflection joins. The exhaustion
uses the general theorem on two elementary subgroups of index two.
-/

public section
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {K : Type*} [Group K] [Finite K]

/-- A central elementary eight and an inverted cyclic four have exactly
the two displayed elementary-sixteen extensions after adjoining an external
involution. All subgroups and generators remain in the original group. -/
theorem elementaryEight_dihedral_extension
    (E : Subgroup K) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEZ : E ≤ center K) (c b : K) (hc : orderOf c = 4) (hcE : c ^ 2 ∈ E)
    (hb : b ^ 2 = 1) (hbD : b ∉ E ⊔ zpowers c)
    (hbc : b * c * b⁻¹ = c⁻¹) (hgen : (E ⊔ zpowers c) ⊔ zpowers b = ⊤) :
    let A := E ⊔ zpowers b
    let B := E ⊔ zpowers (c * b)
    Nat.card K = 32 ∧ center K = E ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E ∧
      (∀ F : Subgroup K,
        (E ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  classical
  let D := E ⊔ zpowers c
  let A := E ⊔ zpowers b
  let B := E ⊔ zpowers (c * b)
  have hc4 : c ^ 4 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc2 : c ^ 2 ≠ 1 := by
    intro he
    have hh := orderOf_dvd_of_pow_eq_one he
    rw [hc] at hh
    norm_num at hh
  have hcnot : c ∉ E := fun he => hc2 (elemPow_eq_one_of_isElementaryAbelian c he)
  let : E.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hEZ hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hcentral (x : K) : x ∈ centralizer (E : Set K) := by
    intro e he
    exact (mem_center_iff.mp (hEZ he) x).symm
  have hi : E ⊓ zpowers c = zpowers (c ^ 2) := by
    apply le_antisymm ?_ (le_inf (zpowers_le.mpr hcE)
      (zpowers_le.mpr ((zpowers c).pow_mem (mem_zpowers c) 2)))
    rintro x ⟨hxE, hxc⟩
    change x ∈ zpowers c at hxc
    rw [mem_zpowers_iff_mem_range_orderOf, hc] at hxc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hxc
    have hn4 : n < 4 := Finset.mem_range.mp hn
    interval_cases n
    · simp
    · exact (hcnot (by simpa using hxE)).elim
    · exact mem_zpowers _
    · have he : c ^ 3 * c ^ 2 = c := by
        rw [← pow_add, show 3 + 2 = 4 + 1 by decide, pow_add, hc4]
        simp
      exact (hcnot (he ▸ E.mul_mem hxE hcE)).elim
  have hD : Nat.card D = 16 := by
    have hco : orderOf (c ^ 2) = 2 := orderOf_eq_prime
      (by rw [← pow_mul]; exact hc4) hc2
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E (zpowers c)
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hE, hi, Nat.card_zpowers, Nat.card_zpowers, hc, hco] at hh
    change 8 * 4 = 2 * Nat.card D at hh
    omega
  have hbN : b ∈ normalizer (D : Set K) := by
    have hEb : E.map (MulAut.conj b).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp (show b ∈ normalizer (E : Set K) by
        rw [normalizer_eq_top]; trivial)
    rw [mem_normalizer_iff_map_conj_eq]
    change (E ⊔ zpowers c).map (MulAut.conj b).toMonoidHom = E ⊔ zpowers c
    rw [Subgroup.map_sup, hEb, MonoidHom.map_zpowers]
    change E ⊔ zpowers (b * c * b⁻¹) = E ⊔ zpowers c
    rw [hbc, zpowers_inv]
  have hK : Nat.card K = 32 := by
    have hh := card_sup_zpowers_of_normalizing_involution D b hb hbD hbN
    rw [hgen, card_top, hD] at hh
    exact hh
  have hcb : (c * b) ^ 2 = 1 := by
    calc
      (c * b) ^ 2 = c * (b * c * b⁻¹) * b ^ 2 := by simp only [pow_two]; group
      _ = 1 := by rw [hbc, hb, mul_inv_cancel, one_mul]
  have hbE : b ∉ E := fun he => hbD (mem_sup_left he)
  have hcbE : c * b ∉ E := by
    intro he
    have hh : c * b ∈ D := mem_sup_left he
    have hcc : c ∈ D := mem_sup_right (mem_zpowers c)
    exact hbD ((D.mul_mem_cancel_left hcc).mp hh)
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb
  let : IsElementaryAbelian 2 (zpowers (c * b)) := IsElementaryAbelian.zpowers_of_pow_eq_one hcb
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr (hcentral b))
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr (hcentral (c * b)))
  have hA : Nat.card A = 16 := by
    rw [card_sup_zpowers_of_normalizing_involution E b hb hbE
      (centralizer_le_normalizer _ (hcentral b)), hE]
  have hB : Nat.card B = 16 := by
    rw [card_sup_zpowers_of_normalizing_involution E (c * b) hcb hcbE
      (centralizer_le_normalizer _ (hcentral (c * b))), hE]
  have hiA : A.index = 2 := by
    have hh := A.card_mul_index
    rw [hA, hK] at hh
    omega
  have hiB : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hB, hK] at hh
    omega
  have hne : A ≠ B := by
    intro he
    have hcbA : c * b ∈ A := he ▸ mem_sup_right (mem_zpowers (c * b))
    have hbA : b ∈ A := mem_sup_right (mem_zpowers b)
    have hcA : c ∈ A := by simpa using A.mul_mem hcbA (A.inv_mem hbA)
    exact hc2 (elemPow_eq_one_of_isElementaryAbelian c hcA)
  have hncomm : ¬ IsMulCommutative K := by
    intro hh
    have hcomm := hh.is_comm.comm b c
    have he : c = c⁻¹ := by
      calc
        c = b * c * b⁻¹ := by rw [hcomm, mul_inv_cancel_right]
        _ = c⁻¹ := hbc
    apply hc2
    calc
      c ^ 2 = c * c := pow_two c
      _ = c⁻¹ * c := congrArg (fun x : K => x * c) he
      _ = 1 := inv_mul_cancel c
  have hsup : A ⊔ B = ⊤ := by
    apply top_unique
    rw [← hgen]
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) (zpowers_le.mpr ?_))
      (le_sup_right.trans le_sup_left)
    have hcbAB : c * b ∈ A ⊔ B := mem_sup_right (mem_sup_right (mem_zpowers _))
    have hbAB : b ∈ A ⊔ B := mem_sup_left (mem_sup_right (mem_zpowers _))
    simpa using (A ⊔ B).mul_mem hcbAB ((A ⊔ B).inv_mem hbAB)
  have hinter : A ⊓ B = E := by
    apply Eq.symm
    apply eq_of_le_of_card_ge (le_inf le_sup_left le_sup_left)
    let : A.Normal := A.normal_of_index_eq_two hiA
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hA, hB, hsup, card_top, hK] at hh
    rw [hE]
    change Nat.card (A ⊓ B : Subgroup K) ≤ 8
    omega
  have hZ : center K = E := le_antisymm
    ((le_inf (center_le_abelian_index_two A hiA hncomm)
      (center_le_abelian_index_two B hiB hncomm)).trans_eq hinter) hEZ
  refine ⟨hK, hZ, inferInstance, hA, inferInstance, hB, hne, hinter, ?_⟩
  intro F
  constructor
  · rintro ⟨_, hF, hFc⟩
    rcases elementary_le_one_of_two_index_two A B inferInstance inferInstance hiA hiB hne
      (fun he => hncomm he.toIsMulCommutative) F hF with hFA | hFB
    · exact Or.inl (eq_of_le_of_card_ge hFA (by rw [hA, hFc]))
    · exact Or.inr (eq_of_le_of_card_ge hFB (by rw [hB, hFc]))
  · rintro (rfl | rfl)
    · exact ⟨le_sup_left, inferInstance, hA⟩
    · exact ⟨le_sup_left, inferInstance, hB⟩

end Subgroup
