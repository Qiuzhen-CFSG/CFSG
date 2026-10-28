module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase

/-!
# Inverted elements above an elementary supplement

Suppose the centralizer of a normal omega four is the product of an
elementary subgroup B and a normal abelian base D. If an involution in B
inverts only square-trivial elements of D, every conjugate of it lies in B.
Indeed, write a conjugate as d b. Both it and b are involutions, so it
inverts d, forcing d into the omega four. The normal core of B would then
contain an elementary eight unless the original involution lies in D.

Unlike the central-action obstruction, this argument does not require the
action of the involution to be central in the conjugation image.

Source context: the C₄-square action problem in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3(a), printed p.386.
-/

open Subgroup
namespace IsPGroup

/-- An involution in an elementary supplement must invert a nonbinary base
element unless it belongs to the base. -/
public theorem mem_base_of_binary_inversion_of_elementary_centralizer
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D B : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4)
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (hC : centralizer (W : Set P) = B ⊔ D)
    (x : P) (hxB : x ∈ B)
    (hinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ → d ^ 2 = 1) : x ∈ D := by
  have hx : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxB
  have binary_mem (d : P) (hd : d ∈ D) (hd2 : d ^ 2 = 1) : d ∈ W := by
    rw [← hO]
    refine ⟨⟨d, hd⟩, subset_closure ?_, rfl⟩
    change (⟨d, hd⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using hd2
  have hxCore : x ∈ B.normalCore := by
    intro g
    let y := g * x * g⁻¹
    have hy : y ^ 2 = 1 := by
      change (MulAut.conj g x) ^ 2 = 1
      rw [← map_pow, hx, map_one]
    have hyinv (d : P) (hd : d ∈ D) (hi : y * d * y⁻¹ = d⁻¹) : d ^ 2 = 1 := by
      let c : MulAut P := MulAut.conj g⁻¹
      have hcy : c y = x := by
        simp [c, y, mul_assoc]
      have he := congrArg c hi
      simp only [map_mul, map_inv, hcy] at he
      have hd' : c d ∈ D :=
        (inferInstance : D.Normal).conj_mem d hd g⁻¹
      have hs := hinv _ hd' he
      apply c.injective
      simpa only [map_pow, map_one] using hs
    have hyC : y ∈ centralizer (W : Set P) :=
      (inferInstance : (centralizer (W : Set P)).Normal).conj_mem x
        ((B.le_centralizer.trans (centralizer_le hWB)) hxB) g
    rw [hC, sup_comm] at hyC
    obtain ⟨d, hd, b, hb, hdb⟩ := mem_sup_of_normal_left.mp hyC
    have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hb
    have hdi : y * d * y⁻¹ = d⁻¹ := by
      calc
        y * d * y⁻¹ = y ^ 2 * (b ^ 2)⁻¹ * d⁻¹ := by
          rw [← hdb]
          simp only [pow_two]
          group
        _ = d⁻¹ := by rw [hy, hb2]; simp
    change y ∈ B
    rw [← hdb]
    exact B.mul_mem (hWB (binary_mem d hd (hyinv d hd hdi))) hb
  have hWC : W ≤ B.normalCore := normal_le_normalCore.mpr hWB
  let : IsElementaryAbelian 2 B.normalCore := {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      ((B.le_centralizer (B.normalCore_le a.property)) b
        (B.normalCore_le b.property)).symm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (a : P) (B.normalCore_le a.property)) }
  have hsmall : Nat.card B.normalCore < 8 := by
    by_contra! hlarge
    exact hno ⟨B.normalCore, inferInstance, inferInstance, hlarge⟩
  have hdiv : 4 ∣ Nat.card B.normalCore := hW ▸ card_dvd_of_le hWC
  have heq : W = B.normalCore := eq_of_le_of_card_ge hWC (by
    rw [hW]
    obtain ⟨k, hk⟩ := hdiv
    omega)
  exact (hO ▸ map_subtype_le _) (heq ▸ hxCore)

/-- Every nonidentity action induced by the elementary supplement inverts
an element of the base whose square is nontrivial. -/
public theorem exists_inverted_nonbinary_of_mem_elementary_conj_image
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D B : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4)
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (hC : centralizer (W : Set P) = B ⊔ D)
    (α : MulAut D)
    (hα : α ∈ ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range)
    (hne : α ≠ 1) : ∃ d : D, α d = d⁻¹ ∧ d ^ 2 ≠ 1 := by
  obtain ⟨b, rfl⟩ := hα
  by_contra! hbinary
  have hbD : (b : P) ∈ D :=
    mem_base_of_binary_inversion_of_elementary_centralizer
      hno W D B hW hO hWB hC b b.property (by
        intro d hd hi
        have he : ((MulAut.conjNormal : P →* MulAut D).comp B.subtype) b
            ⟨d, hd⟩ = (⟨d, hd⟩ : D)⁻¹ := Subtype.ext hi
        exact congrArg (fun d : D => (d : P)) (hbinary ⟨d, hd⟩ he))
  apply hne
  apply MulEquiv.ext
  intro d
  apply Subtype.ext
  change (b : P) * (d : P) * (b : P)⁻¹ = d
  rw [(D.le_centralizer hbD d d.property).symm, mul_inv_cancel_right]

end IsPGroup
