module

public import Theory.GroupTheory.ElementarySecondCenterSquareMap

/-!
# Quadraticity of the square map over an elementary second-center subgroup

Suppose D is elementary abelian, contains the commutator subgroup and all
squares, and lies in the second center of K. Modulo Z(K), its elements are
central involutions. The square of a product is the product of the squares
and the commutator; that commutator is bilinear modulo Z(K). Expanding three
factors therefore gives the seven-term quadratic identity in D/(D ∩ Z(K)).

The evaluation interface applies to any construction of the literal square
map, and the final theorem specializes it to elementarySecondCenterSquare.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, the quadratic structure on the core quotients.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Subgroup

private theorem square_mul_of_central {L : Type*} [Group L] (x y : L)
    (hx : x ^ 2 ∈ center L) (hc : ⁅x, y⁆ ∈ center L) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x, y⁆ := by
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x, y⁆ = ⁅x, y⁆ * (x ^ 2 * y ^ 2) :=
      mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
      rw [mem_center_iff.mp hx]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

private theorem seven_term_of_polar {L A : Type*} [Group L] [CommGroup A]
    (q : L → A) (b : L → L → A)
    (hmul : ∀ x y, q (x * y) = q x * q y * b x y)
    (hbi : ∀ x y z, b (x * y) z = b x z * b y z)
    (hq : ∀ x, q x ^ 2 = 1) (hb : ∀ x y, b x y ^ 2 = 1)
    (x y z : L) :
    q (x * y * z) * q (x * y) * q (x * z) * q (y * z) * q x * q y * q z = 1 := by
  simp only [hmul, hbi]
  calc
    _ = (q x ^ 2) ^ 2 * (q y ^ 2) ^ 2 * (q z ^ 2) ^ 2 *
        b x y ^ 2 * b x z ^ 2 * b y z ^ 2 := by simp only [pow_two]; ac_rfl
    _ = 1 := by rw [hq, hq, hq, hb, hb, hb]; simp

private theorem mapped_square_seven_term {K : Type*} [Group K]
    (D : Subgroup K) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D)
    (hcomm : _root_.commutator K ≤ D) (x y z : K) :
    let p := QuotientGroup.mk' (center K)
    p ((x * y * z) ^ 2) * p ((x * y) ^ 2) * p ((x * z) ^ 2) *
      p ((y * z) ^ 2) * p (x ^ 2) * p (y ^ 2) * p (z ^ 2) = 1 := by
  let p := QuotientGroup.mk' (center K)
  have hcentral (d : K) (hd : d ∈ D) : p d ∈ center (K ⧸ center K) := by
    have hh := hD hd
    rw [← Subgroup.comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one] at hh
    exact hh
  have hbracket (a b : K) : ⁅a, b⁆ ∈ D :=
    hcomm (commutator_mem_commutator (mem_top a) (mem_top b))
  let q (a : K) : center (K ⧸ center K) := ⟨p (a ^ 2), hcentral _ (hsq a)⟩
  let b (a c : K) : center (K ⧸ center K) :=
    ⟨p ⁅a, c⁆, hcentral _ (hbracket a c)⟩
  have hmul (a c : K) : q (a * c) = q a * q c * b a c := by
    apply Subtype.ext
    change p ((a * c) ^ 2) = p (a ^ 2) * p (c ^ 2) * p ⁅a, c⁆
    simp only [map_pow, map_mul, map_commutatorElement]
    exact square_mul_of_central _ _
      (by simpa only [map_pow] using hcentral _ (hsq a))
      (by simpa only [map_commutatorElement] using hcentral _ (hbracket a c))
  have hbi (a c d : K) : b (a * c) d = b a d * b c d := by
    apply Subtype.ext
    change p ⁅a * c, d⁆ = p ⁅a, d⁆ * p ⁅c, d⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    simp only [map_mul, map_inv]
    rw [mem_center_iff.mp (hcentral _ (hbracket c d)) (p a)]
    simp only [mul_inv_cancel_right]
    exact (mem_center_iff.mp (hcentral _ (hbracket c d)) (p ⁅a, d⁆)).symm
  have hq (a : K) : q a ^ 2 = 1 := by
    apply Subtype.ext
    change p (a ^ 2) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hsq a), map_one]
  have hb (a c : K) : b a c ^ 2 = 1 := by
    apply Subtype.ext
    change p ⁅a, c⁆ ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hbracket a c), map_one]
  exact congrArg Subtype.val (seven_term_of_polar q b hmul hbi hq hb x y z)

/-- Every map evaluating on actual squares has the seven-term quadratic identity. -/
public theorem square_seven_term_of_evaluation {K : Type*} [Group K]
    (D : Subgroup K) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D)
    (hcomm : _root_.commutator K ≤ D)
    (square : K ⧸ D → D ⧸ (center K).subgroupOf D)
    (heval : ∀ (x : K) (hx : x ^ 2 ∈ D),
      square (QuotientGroup.mk' D x) =
        QuotientGroup.mk' ((center K).subgroupOf D) ⟨x ^ 2, hx⟩)
    (a b c : K ⧸ D) :
    square (a * b * c) * square (a * b) * square (a * c) * square (b * c) *
      square a * square b * square c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D b
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective D c
  have he (j : K) := heval j (hsq j)
  simp only [← map_mul, he]
  apply (QuotientGroup.eq_one_iff _).mpr
  change (x * y * z) ^ 2 * (x * y) ^ 2 * (x * z) ^ 2 * (y * z) ^ 2 *
    x ^ 2 * y ^ 2 * z ^ 2 ∈ center K
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (center K) ((x * y * z) ^ 2 * (x * y) ^ 2 *
    (x * z) ^ 2 * (y * z) ^ 2 * x ^ 2 * y ^ 2 * z ^ 2) = 1
  simpa only [map_mul] using mapped_square_seven_term D hD hsq hcomm x y z

/-- The descended square map is quadratic. -/
public theorem elementarySecondCenterSquare_seven_term {K : Type*} [Group K]
    (D : Subgroup K) [D.Normal] [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D)
    (hcomm : _root_.commutator K ≤ D) (a b c : K ⧸ D) :
    let q := elementarySecondCenterSquare D hD hsq
    q (a * b * c) * q (a * b) * q (a * c) * q (b * c) * q a * q b * q c = 1 :=
  square_seven_term_of_evaluation D hD hsq hcomm
    (elementarySecondCenterSquare D hD hsq)
    (fun x _ => elementarySecondCenterSquare_apply D hD hsq x) a b c

end Subgroup
