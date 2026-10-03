module

public import Theory.GroupTheory.PGroup.C4SquareConjugationImage
public import Theory.GroupTheory.PGroup.C4SquareMaximalExtension
public import Theory.GroupTheory.PGroup.C4SquareSixteenInvertedRoots
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase

/-!
# Elementary actions on a C₄-square with central omega of order two

An elementary subgroup containing the normal omega four acts on a normal
self-centralizing C₄-square with image of order at most four.

The full action has order at most 32. If the elementary image were larger
than four, the index-two centralizer of the normal four forces the full
image to have order 16 or 32. At order 16, the elementary subgroup and the
base generate this centralizer. Hence the central transvection has an
involution lift, contradicting the normal-eight obstruction. At order 32,
the maximal-action lifting theorem supplies that contradiction directly.

This avoids the stronger, false assertion that every elementary action
excludes all five binary-inverter congruence matrices. No uniqueness of the
normal four is needed.

Source: the C₄-square extension arguments of MacWilliams, Trans. AMS 150
(1970), §1.2, and Janko–Thompson, Math. Z. 113 (1970), 1.1 and 1.4.
-/

open Subgroup
namespace IsPGroup

private theorem card_eq_inf_omega_mul_conj_image_of_elementary
    {P : Type*} [Group P] [Finite P]
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card A = Nat.card (A ⊓ W : Subgroup P) *
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp A.subtype
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hk : f.ker.map A.subtype = A ⊓ W := by
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      have haD : (a : P) ∈ D := by
        apply hDC
        intro d hd
        have hh := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P))
          (MonoidHom.mem_ker.mp ha)
        change (a : P) * d * (a : P)⁻¹ = d at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      refine ⟨a.property, ?_⟩
      rw [← hO]
      refine ⟨⟨a, haD⟩, subset_closure ?_, rfl⟩
      change (⟨(a : P), haD⟩ : D) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (a : P) a.property
    · intro a ha
      refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      change a * (d : P) * a⁻¹ = d
      rw [(D.le_centralizer (hWD ha.2) d d.property).symm, mul_inv_cancel_right]
  have hkc : Nat.card f.ker = Nat.card (A ⊓ W : Subgroup P) := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hk
    simpa only [card_map_of_injective A.subtype_injective] using hh
  have hc := f.ker.card_mul_index
  rw [index_ker, hkc] at hc
  exact hc.symm

/-- A normal C₄-square cannot have full conjugation image of order 32 when
normal elementary eights are absent. -/
public theorem c4_square_conj_image_card_ne_thirtytwo
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Nat.card (MulAut.conjNormal : P →* MulAut D).range ≠ 32 := by
  intro hc
  obtain ⟨x, hx, hxD, hfix, hcomm, hinv⟩ :=
    C4SquareExtension.exists_involution_central_binary_action hP D hDC ⟨e⟩ hc
  apply hno
  apply exists_normal_eight_of_involution_central_action W D hW hDC hO x hx hxD
  · intro w hw
    have hwD : w ∈ D := (hO ▸ map_subtype_le _) hw
    have hw2 : (⟨w, hwD⟩ : D) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
    have hh := congrArg Subtype.val (hfix ⟨w, hwD⟩ hw2)
    change x * w * x⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact hcomm
  · intro d hd hi
    exact congrArg Subtype.val (hinv ⟨d, hd⟩ (Subtype.ext hi))

/-- The C₄-square branch of the elementary overgroup action bound, with
central omega of order two. The normal four need not be unique. -/
public theorem conj_image_card_le_four_of_c4_square_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let c : P →* MulAut D := MulAut.conjNormal
  let r := Nat.card (c.comp B.subtype).range
  by_contra! hlarge
  have hrlarge : 4 < r := hlarge
  have hrp : IsPGroup 2 (c.comp B.subtype).range :=
    (hP.to_subgroup B).of_surjective
      (c.comp B.subtype).rangeRestrict (c.comp B.subtype).rangeRestrict_surjective
  have hr8 : 8 ≤ r := by
    obtain ⟨n, hn⟩ := hrp.exists_card_eq
    have hn3 : 3 ≤ n := by
      by_contra! hh
      have hsmall : 2 ^ n ≤ 4 := by interval_cases n <;> decide
      change r = 2 ^ n at hn
      omega
    change r = 2 ^ n at hn
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn3
  have hDcard : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hBcard : Nat.card B = 4 * r := by
    rw [card_eq_inf_omega_mul_conj_image_of_elementary W D hDC hO B,
      inf_eq_right.mpr hWB, hW]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
    (show B ≤ normalizer (D : Set P) from le_normalizer_of_normal)
  rw [inf_comm D B, sup_comm D B,
    elementary_inf_eq_of_omega_one_eq_four W D B hO hWB, hDcard, hW, hBcard] at hprod
  let C := centralizer (W : Set P)
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hsup : B ⊔ D ≤ C := sup_le
    (B.le_centralizer.trans (centralizer_le hWB))
    (D.le_centralizer.trans (centralizer_le hWD))
  have hle := card_le_of_le hsup
  have hCc := C.card_mul_index
  rw [show C.index = 2 from
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two hP hZ W hW] at hCc
  have hDc := D.card_mul_index
  rw [hDcard] at hDc
  have hindex : 8 < D.index := by nlinarith
  have hfull : Nat.card c.range = D.index := by
    rw [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  have hi16 : D.index = 16 := by
    rcases index_cases_of_selfCentralizing_c4_square hP D hDC ⟨e⟩ (by omega) with h | h | h
    · omega
    · exact h
    · exact False.elim (c4_square_conj_image_card_ne_thirtytwo hP hno W D hW hDC hO e
        (hfull.trans h))
  have hC : centralizer (W : Set P) = B ⊔ D := by
    apply (eq_of_le_of_card_ge hsup ?_).symm
    nlinarith
  let F : P →* MulAut C4SquareExtension.Model := (MulAut.congr e).toMonoidHom.comp c
  have hFc : Nat.card F.range = 16 := by
    rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
    exact hfull.trans hi16
  obtain ⟨a, ha, hane, -, hafix, -, hainv, -, -⟩ :=
    C4SquareExtension.SixteenInverted.exists_central_action F.range
      (IsPGroup.of_card (n := 4) hFc) hFc
  obtain ⟨x, hx⟩ := ha
  have hxfix (d : D) (hd : d ^ 2 = 1) : c x d = d := by
    apply e.injective
    have hh := hafix (e d) (by rw [← map_pow, hd, map_one])
    rw [← hx] at hh
    simpa [F] using hh
  obtain ⟨b, hb⟩ :=
    (C4SquareExtension.mem_elementary_conj_image_iff_fix_square_one W D B hDC hO hWB
      hC (c x) ⟨x, rfl⟩).mpr hxfix
  have hba : F (b : P) = a := by
    change (MulAut.congr e) ((c.comp B.subtype) b) = a
    rw [hb]
    exact hx
  have hbD : (b : P) ∉ D := by
    intro hh
    have hk : (b : P) ∈ c.ker := by
      rwa [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
    apply hane
    rw [← hba]
    change (MulAut.congr e) (c (b : P)) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
  obtain ⟨d, hd, hdi, hd2⟩ :=
    C4SquareExtension.exists_inverted_root_of_action_card_sixteen hno W D hW hDC hO e
      (hfull.trans hi16) b (elemPow_eq_one_of_isElementaryAbelian (b : P) b.property)
      hbD ((B.le_centralizer.trans (centralizer_le hWB)) b.property)
  have he : a (e ⟨d, hd⟩) = (e ⟨d, hd⟩)⁻¹ := by
    rw [← hba]
    change e (c (b : P) (e.symm (e ⟨d, hd⟩))) = (e ⟨d, hd⟩)⁻¹
    rw [e.symm_apply_apply, ← map_inv]
    exact congrArg e (Subtype.ext hdi)
  have hh : (⟨d, hd⟩ : D) ^ 2 = 1 :=
    e.injective (by simpa only [map_pow, map_one] using hainv (e ⟨d, hd⟩) he)
  exact hd2 (congrArg Subtype.val hh)

end IsPGroup
