module

public import Theory.ElementaryAbelian.AnisotropicQuadratic
public import Theory.GroupTheory.PGroup.TransitiveInvolutions
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient

/-!
# Order reductions for groups with three transitive involutions

For a nonabelian finite two-group of exponent four with central,
automorphism-transitive involutions, the special-group calculation identifies
the center, derived subgroup and Frattini subgroup. Three involutions therefore
give an elementary center of order four.

Automorphisms identify the three nonidentity square fibers, so the group order
is four modulo three. A central elementary quotient of order four would force
the derived subgroup to have order at most two. These observations show that an
upper bound of 64 suffices to determine the order exactly. The square map on the
central quotient is anisotropic and has bilinear polar map. Chevalley–Warning
bounds the quotient order by sixteen, giving the required upper bound and
hence group order 64.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1,
printed pp.386 and 393. The square-map construction follows the quotient-lift
argument in `SmallNonabelianTwoGroupAutomorphismOrderFiveSquare`, generalized
from a center of order two to an arbitrary elementary binary center.
-/

open Subgroup
open scoped commutatorElement

namespace IsPGroup

/-- An elementary center containing all involutions has order four if there are
exactly three involutions. -/
public theorem card_center_of_three_central_involutions
    {P : Type*} [Group P] [Finite P]
    [IsElementaryAbelian 2 (center P)]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3) :
    Nat.card (center P) = 4 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : {x : P // orderOf x = 2} ≃ {z : center P // z ≠ 1} :=
    { toFun := fun x => ⟨⟨x, hcentral x (orderOf_eq_prime_iff.mp x.property).1⟩,
        fun he => (orderOf_eq_prime_iff.mp x.property).2 (congrArg Subtype.val he)⟩
      invFun := fun z => ⟨z.val, orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (z.val : P) z.val.property)
        (fun he => z.property (Subtype.ext he))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype (center P) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl] at hthree
  simp only [Fintype.card_subtype_eq] at hthree
  rw [Nat.card_eq_fintype_card]
  omega

/-- Automorphism-transitive involutions have equally many square roots. -/
public theorem card_square_fiber_eq_of_transitive_involutions
    {P : Type*} [Group P] [Finite P]
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    {x y : P} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    Nat.card {z : P // z ^ 2 = x} = Nat.card {z : P // z ^ 2 = y} := by
  obtain ⟨a, ha⟩ := htrans x y hx hy
  apply Nat.card_congr (Equiv.subtypeEquiv a.toEquiv ?_)
  intro z
  change z ^ 2 = x ↔ (a z) ^ 2 = y
  rw [← map_pow, ← ha, a.injective.eq_iff]

/-- Partition into the identity square fiber and the three equal involution
square fibers. -/
public theorem card_eq_four_add_three_mul_square_fiber
    {P : Type*} [Group P] [Finite P]
    [IsElementaryAbelian 2 (center P)]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) (z : P) (hz : orderOf z = 2) :
    Nat.card P = 4 + 3 * Nat.card {x : P // x ^ 2 = z} := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype {x : P // orderOf x = 2} := Fintype.ofFinite _
  have hfour : Nat.card {x : P // x ^ 2 = 1} = 4 := by
    have he : {x : P // x ^ 2 = 1} ≃ center P :=
      Equiv.subtypeEquivRight fun x =>
        ⟨hcentral x, elemPow_eq_one_of_isElementaryAbelian x⟩
    rw [Nat.card_congr he]
    exact card_center_of_three_central_involutions hcentral hthree
  have he := Equiv.sigmaSubtypeFiberEquivSubtype (fun x : P => x ^ 2)
    (p := fun x => x ^ 2 ≠ 1) (q := fun x => orderOf x = 2) (fun x => by
      exact ⟨fun hx => orderOf_eq_prime (by simpa only [← pow_mul] using hexp x) hx,
        fun hx => (orderOf_eq_prime_iff.mp hx).2⟩)
  have hrest : Nat.card {x : P // x ^ 2 ≠ 1} =
      3 * Nat.card {x : P // x ^ 2 = z} := by
    rw [← Nat.card_congr he, Nat.card_sigma]
    have hf (y : {x : P // orderOf x = 2}) :
        Nat.card {x : P // x ^ 2 = (y : P)} = Nat.card {x : P // x ^ 2 = z} :=
      card_square_fiber_eq_of_transitive_involutions htrans y.property hz
    simp_rw [hf]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hthree]
  have hsum := Nat.card_congr (Equiv.sumCompl (fun x : P => x ^ 2 = 1))
  rw [Nat.card_sum, hfour, hrest] at hsum
  exact hsum.symm

/-- A group with central commutators and central involutions has elementary
central quotient when its exponent divides four. -/
public theorem elementary_center_quotient_of_exponent_four
    {P : Type*} [Group P] (hD : commutator P ≤ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hexp : ∀ x : P, x ^ 4 = 1) : IsElementaryAbelian 2 (P ⧸ center P) := by
  refine {
    toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr hD
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr
      (hcentral _ (by simpa only [← pow_mul] using hexp x))

/-- The special-group structure and square-fiber counts determine the group
order once an upper bound of 64 is known. -/
public theorem card_eq_sixty_four_of_three_involutions_of_card_le
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) (hbound : Nat.card P ≤ 64) :
    Nat.card P = 64 := by
  obtain ⟨hD, _, hE, _⟩ :=
    hP.special_of_exponent_four_of_transitive_involutions hnonab hcentral htrans hexp
  let : IsElementaryAbelian 2 (center P) := hE
  have hZ := card_center_of_three_central_involutions hcentral hthree
  have hZlt : 4 < Nat.card P := by
    rw [← hZ]
    have hle := Nat.card_le_card_of_injective (center P).subtype (center P).subtype_injective
    have hne : Nat.card (center P) ≠ Nat.card P := fun he =>
      hnonab (center_eq_top_iff.mp ((center P).eq_top_of_card_eq he))
    omega
  have hI : Nonempty {x : P // orderOf x = 2} :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card {x : P // orderOf x = 2} by omega)).1
  obtain ⟨z⟩ := hI
  have hcount := card_eq_four_add_three_mul_square_fiber hcentral hthree htrans hexp z z.property
  have h16 : Nat.card P ≠ 16 := by
    intro h16
    have hquot : Nat.card (P ⧸ center P) = 4 := by
      have hh := card_eq_card_quotient_mul_card_subgroup (center P)
      rw [h16, hZ] at hh
      omega
    let : IsElementaryAbelian 2 (P ⧸ center P) :=
      elementary_center_quotient_of_exponent_four hD.symm.le hcentral hexp
    have hd := card_commutator_le_two_of_central_elementary_four_quotient
      (center P) le_rfl hquot
    rw [← hD, hZ] at hd
    omega
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hnle : n ≤ 6 := by
    have hh : 2 ^ n ≤ 2 ^ 6 := hn ▸ hbound
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  rw [hn] at hZlt hcount h16 ⊢
  interval_cases n <;> norm_num at hcount ⊢ <;> omega

/-- Squaring descends to an anisotropic quadratic map on the central quotient
when the center is elementary, all involutions are central and the exponent
divides four. The polar map is the group commutator. -/
public theorem exists_anisotropic_center_quotient_square_map
    {P : Type*} [Group P] [IsElementaryAbelian 2 (center P)]
    (hD : commutator P ≤ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hexp : ∀ x : P, x ^ 4 = 1) :
    ∃ (square : P ⧸ center P → center P)
      (polar : P ⧸ center P → P ⧸ center P → center P),
      square 1 = 1 ∧
      (∀ x y, square (x * y) = square x * square y * polar x y) ∧
      (∀ x y z, polar (x * y) z = polar x z * polar y z) ∧
      (∀ x, square x = 1 → x = 1) := by
  have hsq (x : P) : x ^ 2 ∈ center P :=
    hcentral _ (by simpa only [← pow_mul] using hexp x)
  have hZ (z : P) (hz : z ∈ center P) : z ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian z hz
  have hsame (x y : P)
      (hxy : QuotientGroup.mk' (center P) x = QuotientGroup.mk' (center P) y) :
      x ^ 2 = y ^ 2 := by
    have hm : x⁻¹ * y ∈ center P := QuotientGroup.eq.mp hxy
    have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp hm x
    have he := hc.mul_pow 2
    simpa only [mul_inv_cancel_left, hZ _ hm, mul_one] using he.symm
  let square : P ⧸ center P → center P :=
    Quotient.lift (fun x => ⟨x ^ 2, hsq x⟩) (by
      intro x y hxy
      exact Subtype.ext (hsame x y (Quotient.sound hxy)))
  have hsquare (x : P) : (square (QuotientGroup.mk' (center P) x) : P) = x ^ 2 := rfl
  let polar (x y : P ⧸ center P) : center P :=
    (square x * square y)⁻¹ * square (x * y)
  have hcomm (x y : P) : ⁅x,y⁆ ∈ center P :=
    hD (commutator_mem_commutator (mem_top x) (mem_top y))
  have hmul (x y : P) : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
    have hx : ∀ z : P, z * x ^ 2 = x ^ 2 * z := mem_center_iff.mp (hsq x)
    have hc : ∀ z : P, z * ⁅x,y⁆ = ⁅x,y⁆ * z := mem_center_iff.mp (hcomm x y)
    symm
    calc
      x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := hc _
      _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
        simp only [commutatorElement_def, mul_assoc]
      _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [hx]
      _ = (x * y) ^ 2 := by simp only [pow_two]; group
  have hpolar (x y : P) :
      (polar (QuotientGroup.mk' (center P) x) (QuotientGroup.mk' (center P) y) : P) =
        ⁅x,y⁆ := by
    change (x ^ 2 * y ^ 2)⁻¹ * (x * y) ^ 2 = _
    rw [hmul, inv_mul_cancel_left]
  refine ⟨square, polar, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (one_pow 2)
  · intro x y
    simp only [polar, mul_inv_cancel_left]
  · intro x y z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z =>
          apply Subtype.ext
          change (polar (QuotientGroup.mk' (center P) (x * y))
              (QuotientGroup.mk' (center P) z) : P) =
            (polar (QuotientGroup.mk' (center P) x) (QuotientGroup.mk' (center P) z) : P) *
            (polar (QuotientGroup.mk' (center P) y) (QuotientGroup.mk' (center P) z) : P)
          simp only [hpolar]
          rw [commutatorElement_mul_left_eq_conj_mul]
          have hc := mem_center_iff.mp (hcomm y z)
          rw [hc x]
          simp only [mul_assoc, mul_inv_cancel, mul_one]
          exact (hc ⁅x,z⁆).symm
  · intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply (QuotientGroup.eq_one_iff x).mpr
      exact hcentral x (congrArg Subtype.val hx)


/-- A nonabelian finite two-group of exponent four with exactly three central,
automorphism-transitive involutions has order 64. -/
public theorem card_eq_sixty_four_of_exponent_four_of_transitive_three_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) : Nat.card P = 64 := by
  obtain ⟨hD, _, hE, _⟩ :=
    hP.special_of_exponent_four_of_transitive_involutions hnonab hcentral htrans hexp
  let : IsElementaryAbelian 2 (center P) := hE
  let : IsElementaryAbelian 2 (P ⧸ center P) :=
    elementary_center_quotient_of_exponent_four hD.symm.le hcentral hexp
  have hZ := card_center_of_three_central_involutions hcentral hthree
  obtain ⟨square, polar, hone, hquadratic, hbilinear, hanisotropic⟩ :=
    exists_anisotropic_center_quotient_square_map hD.symm.le hcentral hexp
  have hquot := IsElementaryAbelian.card_le_sixteen_of_anisotropic_quadratic
    hZ square polar hone hquadratic hbilinear hanisotropic
  have hcard := card_eq_card_quotient_mul_card_subgroup (center P)
  rw [hZ] at hcard
  exact hP.card_eq_sixty_four_of_three_involutions_of_card_le
    hnonab hcentral hthree htrans hexp (by omega)

end IsPGroup
