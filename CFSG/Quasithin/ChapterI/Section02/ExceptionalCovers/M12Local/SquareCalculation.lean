module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.Definitions
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The M₁₂ local square-count deduction

For structural square coordinates on the actual core, the binary cubic
census excludes c=3 and c=9 in the literal quotient R/⟨v₄⟩ modulo the image
of Z(K). Its parity identity forces v₄=v₅, which gives the unique square
in the specified central coset. A retraction of C_K(u) onto Z(K) contradicts
source restriction (i); this excludes an involutory noncentral lift once
the elementary-branch retraction has been constructed.

The coordinate construction and that retraction remain explicit premises.
This module does not yet assert the complete M₁₂ row of I.2.2. Their
construction and final source assembly belong to this local development.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open Theory.LinearAlgebra.BinaryCubicOrbits
variable {K : Type*} [Group K]

namespace SquareCoordinates
variable {u : K} (d : SquareCoordinates u)

theorem first_axis_zero : d.quadratic (rep 3) = 0 := by
  rw [← d.root_coordinates]
  exact (d.square_kernel d.root).mpr (mem_zpowers _)

theorem second_axis_zero : d.quadratic (rep 4) = 0 :=
  last_value_zero d.quadratic d.invariant d.noncentral_fusion d.central_lift d.first_axis_zero

theorem root_square_mark :
    QuotientGroup.mk' (center K) ((d.root : K) ^ 2) = QuotientGroup.mk' (center K) u := by
  apply (d.square_over_u d.root).mpr
  rw [d.root_coordinates]
  decide +kernel

private theorem mem_zpowers_of_square_one {G : Type*} [Group G] {a x : G}
    (ha : a ^ 2 = 1) (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  classical
  have hf : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ha⟩
  by_cases h1 : a = 1
  · simpa [h1] using hx
  have ho : orderOf a = 2 := orderOf_eq_prime ha h1
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hix.symm)
  · exact Or.inr (by simpa using hix.symm)

theorem square_eq_root_square (hu : u ∉ center K) (r : centralizerCore u)
    (hr : QuotientGroup.mk' (center K) ((r : K) ^ 2) = QuotientGroup.mk' (center K) u) :
    r ^ 2 = d.root ^ 2 := by
  have hq := zero_on_order_four d.quadratic d.invariant d.noncentral_fusion
    d.central_lift d.first_axis_zero (d.coordinates r).toAdd ((d.square_over_u r).mp hr)
  have hp := (d.square_kernel r).mp hq
  have hv : (d.root ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact d.fourth_power d.root
  rcases mem_zpowers_of_square_one hv hp with h | h
  · exfalso
    apply hu
    apply (QuotientGroup.eq_one_iff u).mp
    change QuotientGroup.mk' (center K) u = 1
    rw [← hr]
    have hh : (r : K) ^ 2 = 1 := congrArg Subtype.val h
    rw [hh, map_one]
  · exact h

theorem exists_second_axis_equal_square (hu : u ∉ center K) :
    ∃ r₅ : centralizerCore u,
      (d.coordinates r₅).toAdd = rep 4 ∧ r₅ ^ 2 = d.root ^ 2 := by
  obtain ⟨r, hr⟩ := d.coordinates_surjective (Multiplicative.ofAdd (rep 4))
  have hc : (d.coordinates r).toAdd = rep 4 := congrArg Multiplicative.toAdd hr
  refine ⟨r, hc, d.square_eq_root_square hu r ?_⟩
  apply (d.square_over_u r).mpr
  rw [hc]
  decide +kernel

include d in
theorem hasUniqueCoreSquareLift (hu : u ∉ center K) : HasUniqueCoreSquareLift u := by
  refine ⟨(d.root : K) ^ 2, ⟨d.root_square_mark, d.root, d.root.property, rfl⟩, ?_⟩
  rintro v ⟨hv, x, hx, rfl⟩
  exact congrArg Subtype.val (d.square_eq_root_square hu ⟨x, hx⟩ hv)

/-- The actual line V₄ inside R, not the center of the ambient cover. -/
def squareLine : Subgroup (centralizerCore u) := zpowers (d.root ^ 2)

theorem squareLine_le_center : d.squareLine ≤ center (centralizerCore u) :=
  zpowers_le.mpr (d.square_central d.root)

instance squareLine_normal : d.squareLine.Normal := by
  constructor
  intro x hx g
  have hc := mem_center_iff.mp (d.squareLine_le_center hx) g
  simpa only [hc, mul_inv_cancel_right] using hx

theorem square_in_quotient_eq_one_iff (r : centralizerCore u) :
    (QuotientGroup.mk' d.squareLine r) ^ 2 = 1 ↔
      d.quadratic (d.coordinates r).toAdd = 0 := by
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (r ^ 2)).trans (d.square_kernel r).symm

theorem quotient_order_four_iff (r : centralizerCore u) :
    orderOf (QuotientGroup.mk' d.squareLine r) = 4 ↔
      d.quadratic (d.coordinates r).toAdd ≠ 0 := by
  rw [ne_eq, ← d.square_in_quotient_eq_one_iff r]
  constructor
  · intro h hs
    have ho := orderOf_dvd_of_pow_eq_one hs
    rw [h] at ho
    omega
  · intro h
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one] using h
    · change (QuotientGroup.mk' d.squareLine r) ^ 4 = 1
      rw [← map_pow, d.fourth_power, map_one]

/-- The center coordinates keep the literal first quotient map. -/
noncomputable def centralCoordinates :
    (centralizerCore u) ⧸ center (centralizerCore u) ≃* Multiplicative Space :=
  (QuotientGroup.quotientMulEquivOfEq d.coordinates_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.coordinates d.coordinates_surjective)

theorem centralCoordinates_mk (r : centralizerCore u) :
    d.centralCoordinates (QuotientGroup.mk' (center (centralizerCore u)) r) =
      d.coordinates r := rfl

/-- The source Z-bar is the image of the ambient center Z(K) in R/V₄. -/
def quotientCenter : Subgroup ((centralizerCore u) ⧸ d.squareLine) :=
  ((center K).subgroupOf (centralizerCore u)).map (QuotientGroup.mk' d.squareLine)

instance quotientCenter_normal : d.quotientCenter.Normal := inferInstanceAs
  (((center K).subgroupOf (centralizerCore u)).map (QuotientGroup.mk' d.squareLine)).Normal

theorem center_image_eq :
    (center (centralizerCore u)).map (QuotientGroup.mk' d.squareLine) = d.quotientCenter := by
  rw [d.center_eq, Subgroup.map_sup]
  change d.squareLine.map (QuotientGroup.mk' d.squareLine) ⊔ d.quotientCenter = _
  simp only [QuotientGroup.map_mk'_self, bot_sup_eq]

/-- The literal double quotient in the source is the same binary four-space. -/
noncomputable def doubleQuotientCoordinates :
    (((centralizerCore u) ⧸ d.squareLine) ⧸ d.quotientCenter) ≃* Multiplicative Space :=
  (QuotientGroup.quotientMulEquivOfEq d.center_image_eq.symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient d.squareLine
      (center (centralizerCore u)) d.squareLine_le_center).trans d.centralCoordinates)

theorem doubleQuotientCoordinates_mk (r : centralizerCore u) :
    d.doubleQuotientCoordinates (QuotientGroup.mk' d.quotientCenter
      (QuotientGroup.mk' d.squareLine r)) = d.coordinates r := rfl

/-- The source's c counts cosets containing order-four elements in R/V₄. -/
noncomputable def quotientOrderFourCosetCount : ℕ :=
  Nat.card {c : ((centralizerCore u) ⧸ d.squareLine) ⧸ d.quotientCenter //
    ∃ r : (centralizerCore u) ⧸ d.squareLine,
      QuotientGroup.mk' d.quotientCenter r = c ∧ orderOf r = 4}

theorem quotientOrderFourCosetCount_eq :
    d.quotientOrderFourCosetCount = nonzeroCount d.quadratic := by
  let e : (((centralizerCore u) ⧸ d.squareLine) ⧸ d.quotientCenter) ≃ Space :=
    d.doubleQuotientCoordinates.toEquiv.trans
      ⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro c
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.squareLine r
    rw [← hr]
    exact (d.quotient_order_four_iff x).mp ho
  · intro h
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective d.quotientCenter c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.squareLine r
    exact ⟨_, rfl, (d.quotient_order_four_iff x).mpr h⟩

theorem quotient_count_ne_three_and_nine :
    d.quotientOrderFourCosetCount ≠ 3 ∧ d.quotientOrderFourCosetCount ≠ 9 := by
  rw [d.quotientOrderFourCosetCount_eq]
  exact count_ne_three_and_nine d.quadratic d.invariant


end SquareCoordinates


theorem no_centralizer_retraction (u : K) (hZ : Nat.card (center K) = 2)
    (hrestriction : center K ≤
      (_root_.commutator (centralizer ({u} : Set K))).map
        (centralizer ({u} : Set K)).subtype) : ¬ Nonempty (CentralizerRetraction u) := by
  rintro ⟨d⟩
  have hzero (z : center K) : z = 1 := by
    obtain ⟨c, hc, he⟩ := hrestriction z.property
    have hc' : c = centerToCentralizer u z := Subtype.ext he
    have hz := Abelianization.commutator_subset_ker d.hom hc
    rw [MonoidHom.mem_ker, hc', d.retracts] at hz
    exact hz
  have : Subsingleton (center K) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hc : Nat.card (center K) = 1 := Nat.card_unique
  omega

namespace SquareCoordinates
variable {u : K} (d : SquareCoordinates u)

theorem noncentral_axis_order_four (hZ : Nat.card (center K) = 2)
    (hrestriction : center K ≤
      (_root_.commutator (centralizer ({u} : Set K))).map
        (centralizer ({u} : Set K)).subtype)
    (hsplit : d.quadratic = 0 → Nonempty (CentralizerRetraction u))
    (r : centralizerCore u) (hr : (d.coordinates r).toAdd = rep 0) : orderOf r = 4 := by
  have hsq : r ^ 2 ≠ 1 := by
    intro h
    have hq : d.quadratic (rep 0) = 0 := by
      rw [← hr]
      exact (d.square_kernel r).mpr (h ▸ (zpowers (d.root ^ 2)).one_mem)
    have hzero := zero_of_marked_zero d.quadratic d.invariant d.noncentral_fusion
      d.central_lift d.first_axis_zero hq
    exact no_centralizer_retraction u hZ hrestriction (hsplit hzero)
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one] using hsq
  · exact d.fourth_power r

end SquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
