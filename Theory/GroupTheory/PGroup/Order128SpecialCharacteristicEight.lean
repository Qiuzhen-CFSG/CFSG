module

public import Theory.GroupTheory.PGroup.CharacteristicAbelianSquareKernel
public import Theory.GroupTheory.Commutator.ElementaryCentralQuotient
public import Theory.ElementaryAbelian.BinaryAlternatingPencil

/-!
# A characteristic elementary eight in the special order-128 case

A subgroup of the central quotient isotropic for the commutator pairing has
an abelian inverse image. If every ambient automorphism preserves that
subgroup, its inverse image is characteristic. Its order is the product of
the subgroup order and the center order. A quotient subgroup of order at
least eight therefore supplies an abelian characteristic subgroup of order
at least 32 when the center has order four; the square-kernel argument then
produces a characteristic elementary eight.

When the Frattini subgroup equals the elementary center of order four, the
central quotient is elementary of order 32. Transitivity on the central
involutions gives target transitivity for its commutator pairing. The binary
alternating-pencil theorem constructs the invariant isotropic subgroup, and
the lifting and counting steps above finish the intrinsic structural theorem.

Source context: MacWilliams, Trans. AMS 150 (1970), §4; Janko–Thompson,
Math. Z. 113 (1970), result 1.4(c), printed p.386.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Order128SpecialCharacteristicEight

/-- The original order and Frattini hypotheses provide the binary central
quotient of order 32 and centrality of all squares. -/
public theorem central_quotient_data {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hcard : Nat.card G = 128)
    (hZ : Nat.card (center G) = 4) (hPhi : frattini G = center G) :
    IsElementaryAbelian 2 (G ⧸ center G) ∧
      Nat.card (G ⧸ center G) = 32 ∧ (∀ x : G, x ^ 2 ∈ center G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  have hsq (x : G) : x ^ 2 ∈ center G := by
    rw [← hPhi]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) x
  refine ⟨?_, ?_, hsq⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · apply Normal.quotient_commutative_iff_commutator_le.mpr
      rw [← hPhi]
      exact commutator_le_frattini_of_isPGroup (p := 2)
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsq y)
  · have h := card_eq_card_quotient_mul_card_subgroup (center G)
    rw [hcard, hZ] at h
    omega

private theorem card_comap_center {G : Type*} [Group G] [Finite G]
    (U : Subgroup (G ⧸ center G)) :
    Nat.card (U.comap (QuotientGroup.mk' (center G))) =
      Nat.card U * Nat.card (center G) := by
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero U.index_ne_zero_of_finite)
  calc
    Nat.card (U.comap (QuotientGroup.mk' (center G))) * U.index = Nat.card G := by
      rw [← U.index_comap_of_surjective (QuotientGroup.mk'_surjective (center G))]
      exact (U.comap (QuotientGroup.mk' (center G))).card_mul_index
    _ = Nat.card (G ⧸ center G) * Nat.card (center G) :=
      card_eq_card_quotient_mul_card_subgroup (center G)
    _ = (Nat.card U * Nat.card (center G)) * U.index := by
      rw [← U.card_mul_index]
      ac_rfl

private theorem commutative_comap {G : Type*} [Group G] [Finite G]
    (b : (G ⧸ center G) →* ((G ⧸ center G) →* center G))
    (hb : ∀ x y : G, (b (QuotientGroup.mk' (center G) x)
      (QuotientGroup.mk' (center G) y) : G) = ⁅x, y⁆)
    (U : Subgroup (G ⧸ center G))
    (hU : ∀ x ∈ U, ∀ y ∈ U, b x y = 1) :
    IsMulCommutative (U.comap (QuotientGroup.mk' (center G))) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← hb]
  exact congrArg Subtype.val (hU _ x.property _ y.property)

/-- An invariant isotropic subgroup of order at least eight in the central
quotient gives the required characteristic elementary subgroup upstairs. -/
public theorem exists_of_invariant_isotropic {G : Type*} [Group G] [Finite G]
    (hZ : Nat.card (center G) = 4)
    (hsq : ∀ x : G, x ^ 2 ∈ center G)
    (b : (G ⧸ center G) →* ((G ⧸ center G) →* center G))
    (hb : ∀ x y : G, (b (QuotientGroup.mk' (center G) x)
      (QuotientGroup.mk' (center G) y) : G) = ⁅x, y⁆)
    (hequiv : ∀ a : MulAut G,
      ∃ (v : MulAut (G ⧸ center G)) (w : MulAut (center G)),
        (∀ x : G, QuotientGroup.mk' (center G) (a x) = v (QuotientGroup.mk' (center G) x)) ∧
        ∀ x y, b (v x) (v y) = w (b x y))
    (U : Subgroup (G ⧸ center G)) (hcardU : 8 ≤ Nat.card U)
    (hU : ∀ x ∈ U, ∀ y ∈ U, b x y = 1)
    (hinv : ∀ (v : MulAut (G ⧸ center G)) (w : MulAut (center G)),
      (∀ x y, b (v x) (v y) = w (b x y)) → U.map v.toMonoidHom = U) :
    ∃ E : Subgroup G, E.Characteristic ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let A := U.comap (QuotientGroup.mk' (center G))
  let : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨v, w, hv, hw⟩ := hequiv a
    change QuotientGroup.mk' (center G) (a x) ∈ U
    rw [hv, ← hinv v w hw]
    exact mem_map_of_mem v.toMonoidHom hx
  let : IsMulCommutative A := commutative_comap b hb U hU
  have hA : 32 ≤ Nat.card A := by
    rw [show Nat.card A = Nat.card U * Nat.card (center G) from card_comap_center U, hZ]
    omega
  exact IsPGroup.exists_characteristic_elementary_eight_of_abelian hZ.le hsq A hA

/-- A group of order 128 whose Frattini subgroup is its elementary center of
order four has a characteristic elementary subgroup of order at least eight
if its automorphisms act transitively on central involutions. -/
public theorem exists_characteristic_elementary_eight {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hcard : Nat.card G = 128)
    [IsElementaryAbelian 2 (center G)]
    (hZ : Nat.card (center G) = 4) (hPhi : frattini G = center G)
    (htrans : ∀ x y : G, x ∈ center G → y ∈ center G →
      orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut G, a x = y) :
    ∃ E : Subgroup G, E.Characteristic ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  obtain ⟨hQ, hcardQ, hsq⟩ := central_quotient_data hG hcard hZ hPhi
  let := hQ
  obtain ⟨b, hb, halt, hsep, htransb, hequiv⟩ :=
    exists_elementary_central_quotient_commutator_pairing htrans
  obtain ⟨U, hcardU, hU, hinv⟩ :=
    BinaryAlternatingPencil.exists_invariant_isotropic hcardQ hZ b halt hsep htransb
  exact exists_of_invariant_isotropic hZ hsq b hb hequiv U hcardU hU hinv

end Order128SpecialCharacteristicEight
