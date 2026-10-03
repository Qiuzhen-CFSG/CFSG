module

public import Theory.GroupTheory.PGroup.CentralInvolutionRoots
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini

/-!
# Square classes in a class-two central quotient

Suppose a finite group has central commutators and central involutions, and
every involution has a central square root. Squaring representatives embeds
first omega of the central quotient into the center modulo its squares.
For injectivity, equal square classes make the quotient of the representatives
have square equal to a central square times a commutator. That commutator is
an involution, so its central root corrects the square; the resulting
involution is central. The square kernel and cokernel on the finite abelian
center have equal orders, yielding an omega-order bound.

Exactly three central involutions therefore bound first omega of the central
quotient by four. This is an elementary square-map reduction for the
three-involution structure problem in Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3 and Lemma 5.1.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace IsPGroup

private theorem square_mul_of_square_central
    {P : Type*} [Group P] (hclass : commutator P ≤ center P)
    (x y : P) (hx : x ^ 2 ∈ center P) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
  have hc : ⁅x,y⁆ ∈ center P :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [mem_center_iff.mp hx]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

private theorem commutator_square_eq_one_of_square_central
    {P : Type*} [Group P] (hclass : commutator P ≤ center P)
    (x y : P) (hx : x ^ 2 ∈ center P) : ⁅x,y⁆ ^ 2 = 1 := by
  have hc : ⁅x,y⁆ ∈ center P :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  have hh : ⁅x ^ 2,y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp hx y).symm
  rwa [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two] at hh

/-- The square map on the first omega subgroup of the central quotient is
injective modulo the central squares if involutions have central roots. -/
public theorem card_omega_center_quotient_le_of_central_square_roots
    {P : Type*} [Group P] [Finite P]
    (hclass : commutator P ≤ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hroots : ∀ t : P, t ^ 2 = 1 → ∃ z : center P, (z : P) ^ 2 = t) :
    Nat.card (omega₁ (P ⧸ center P) (p := 2)) ≤
      Nat.card (omega₁ (center P) (p := 2)) := by
  classical
  let : IsMulCommutative (P ⧸ center P) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hclass
  let : CommGroup (P ⧸ center P) := IsMulCommutative.instCommGroup
  let Q := P ⧸ center P
  let q : P →* Q := QuotientGroup.mk' (center P)
  let S := (powMonoidHom 2 : center P →* center P).range
  let r := QuotientGroup.mk' S
  have hlift (a : omega₁ Q (p := 2)) : ∃ x : P, q x = (a : Q) :=
    QuotientGroup.mk'_surjective (center P) a
  choose lift hlift using hlift
  have hsq (a : omega₁ Q (p := 2)) : (lift a) ^ 2 ∈ center P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((lift a)^2) = 1
    rw [map_pow, hlift]
    exact (show (a : Q) ∈ (powMonoidHom 2 : Q →* Q).ker from
      (square_ker_eq_omega_one (A := Q)).symm ▸ a.property)
  let f (a : omega₁ Q (p := 2)) : center P ⧸ S := r ⟨(lift a)^2, hsq a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hdiff : (⟨(lift a)^2, hsq a⟩ : center P)⁻¹ *
        ⟨(lift b)^2, hsq b⟩ ∈ S := QuotientGroup.eq.mp hab
    obtain ⟨z, hz⟩ := hdiff
    have hzP : (z : P)^2 = ((lift a)^2)⁻¹ * (lift b)^2 := congrArg Subtype.val hz
    have ha : ((lift a)⁻¹)^2 ∈ center P := by
      rw [inv_pow]
      exact (center P).inv_mem (hsq a)
    obtain ⟨w, hw⟩ := hroots ⁅(lift a)⁻¹,lift b⁆
      (commutator_square_eq_one_of_square_central hclass _ _ ha)
    have hs : ((lift a)⁻¹ * lift b)^2 = ((z * w : center P) : P)^2 := by
      rw [square_mul_of_square_central hclass _ _ ha, inv_pow, ← hzP, ← hw]
      exact (show Commute (z : P) (w : P) from mem_center_iff.mp w.property z).mul_pow 2 |>.symm
    have hc := mem_center_of_square_eq_central_square hcentral _ (z * w) hs
    apply Subtype.ext
    rw [← hlift a, ← hlift b]
    exact QuotientGroup.eq.mpr hc
  have hbound := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card (center P ⧸ S) = Nat.card (omega₁ (center P) (p := 2)) := by
    rw [← index_eq_card, index_range, square_ker_eq_omega_one]
  exact hbound.trans_eq hcard

/-- Exactly three central involutions give first omega of the center order four. -/
public theorem card_omega_center_eq_four_of_three_central_involutions
    {P : Type*} [Group P] [Finite P]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3) :
    Nat.card (omega₁ (center P) (p := 2)) = 4 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← square_ker_eq_omega_one]
  let K := (powMonoidHom 2 : center P →* center P).ker
  let e : {x : P // orderOf x = 2} ≃ {z : K // z ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨⟨x, hcentral x (orderOf_eq_prime_iff.mp x.property).1⟩,
          Subtype.ext (orderOf_eq_prime_iff.mp x.property).1⟩,
          fun he => (orderOf_eq_prime_iff.mp x.property).2
            (congrArg (fun z : K => ((z : center P) : P)) he)⟩
      invFun := fun z => ⟨((z.val : center P) : P), orderOf_eq_prime
        (congrArg Subtype.val z.val.property)
        (fun he => z.property (Subtype.ext (Subtype.ext he)))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype K := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl] at hthree
  simp only [Fintype.card_subtype_eq] at hthree
  change Nat.card K = 4
  rw [Nat.card_eq_fintype_card]
  omega

end IsPGroup
