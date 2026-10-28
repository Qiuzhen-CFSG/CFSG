module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.PGroup.NormalAbelianIndexFour

/-!
# Order bounds from a normal core with central involutions

A normal subgroup of order sixteen with center of order four and central
involutions forces a two-group containing an elementary sixteen to have
order at least 128, if its central first omega has order two. Indeed, at
order at most 64 the two subgroups would generate the ambient group and
intersect in the whole center of the core. This four-group would then be
ambient-central, a contradiction.

For a critical subgroup, conjugation also expresses the ambient order as
the product of the core-center order and the action-image order. Together
these facts reduce the order-128 problem to constructing the core and
bounding its action image by 32.

Source context: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3,
printed p.386; Thompson's critical subgroup theorem, Gorenstein,
*Finite Groups*, Theorem 5.3.11. No classification is used here.
-/

open Subgroup

/-- A normal sixteen with central involutions and center of order four forces
order at least 128 in the presence of an elementary sixteen and central omega two. -/
public theorem IsPGroup.card_ge_128_of_normal_sixteen
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (C : Subgroup P) [C.Normal] (hC : Nat.card C = 16)
    (hCZ : Nat.card (center C) = 4)
    (hinv : ∀ x : C, x ^ 2 = 1 → x ∈ center C) : 128 ≤ Nat.card P := by
  let Z := (center C).map C.subtype
  have hZC : Z ≤ C := map_subtype_le _
  have hZcard : Nat.card Z = 4 := by
    rw [card_map_of_injective C.subtype_injective, hCZ]
  have hIZ : B ⊓ C ≤ Z := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, hinv _ ?_, rfl⟩
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x hx.1
  have hI : Nat.card (B ⊓ C : Subgroup P) ≤ 4 :=
    (card_le_of_le hIZ).trans_eq hZcard
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B
    (show B ≤ normalizer (C : Set P) from le_normalizer_of_normal)
  rw [inf_comm C B, sup_comm C B, hC, hB] at hprod
  have hlarge : 64 < Nat.card P := by
    by_contra! hsmall
    have hsup : Nat.card (B ⊔ C : Subgroup P) ≤ 64 :=
      (B ⊔ C).card_le_card_group.trans hsmall
    have hIfour : Nat.card (B ⊓ C : Subgroup P) = 4 := by nlinarith
    have hIZeq : B ⊓ C = Z := eq_of_le_of_card_ge hIZ (by omega)
    have hZB : Z ≤ B := hIZeq ▸ inf_le_left
    have htop : B ⊔ C = ⊤ := by
      apply eq_top_of_card_eq
      rw [hIfour] at hprod
      have hh := (B ⊔ C).card_le_card_group
      omega
    have hBC : B ≤ centralizer (Z : Set P) := by
      intro b hb z hz
      exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨z, hZB hz⟩ : B) (⟨b, hb⟩ : B))
    have hCC : C ≤ centralizer (Z : Set P) := by
      intro c hc z hz
      obtain ⟨z, hz, rfl⟩ := hz
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨c, hc⟩).symm
    have hcentral : Z ≤ center P := by
      intro z hz
      apply mem_center_iff.mpr
      intro x
      have hx : x ∈ B ⊔ C := by rw [htop]; trivial
      exact ((sup_le hBC hCC hx) z hz).symm
    have hO : Z ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
      intro z hz
      refine ⟨⟨z, hcentral hz⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      simpa using elemPow_eq_one_of_isElementaryAbelian z (hZB hz)
    have hh := card_le_of_le hO
    rw [hZcard, card_map_of_injective (center P).subtype_injective, hZ] at hh
    omega
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hnlarge : 6 < n := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [hn] using hlarge
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hnlarge

/-- Conjugation on a critical subgroup counts the ambient group, with kernel
exactly the image of the core's center. -/
public theorem IsCriticalPSubgroup.card_eq_center_card_mul_conj_image
    {P : Type*} [Group P] [Finite P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) :
    letI : C.Characteristic := hC.characteristic
    Nat.card P = Nat.card (center C) * Nat.card (MulAut.conjNormal : P →* MulAut C).range := by
  let : C.Characteristic := hC.characteristic
  have hker : (MulAut.conjNormal : P →* MulAut C).ker =
      (center C).map C.subtype := by
    rw [← hC.centralizer_eq]
    ext x
    constructor
    · intro hx c hc
      have hh := congrArg (fun f : MulAut C => (f ⟨c, hc⟩ : P))
        (MonoidHom.mem_ker.mp hx)
      change x * c * x⁻¹ = c at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply MonoidHom.mem_ker.mpr
      ext c
      change x * (c : P) * x⁻¹ = c
      rw [← hx c c.property, mul_inv_cancel_right]
  have hh := (MulAut.conjNormal : P →* MulAut C).ker.card_mul_index
  rw [index_ker, hker, card_map_of_injective C.subtype_injective] at hh
  exact hh.symm
