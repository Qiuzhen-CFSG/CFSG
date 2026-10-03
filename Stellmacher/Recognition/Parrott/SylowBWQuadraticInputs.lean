module

public import Stellmacher.Recognition.Parrott.SylowBWSquareInputs
public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.GroupTheory.ElementarySecondCenterSquareMap

/-!
# Literal inputs for Parrott's quadratic core model

The abelianization of the actual core and its derived central quotient are
both elementary abelian of order sixteen. Squaring descends between these
quotients, has a nontrivial zero supplied by the given involution, and
intertwines every pair of actions evaluating as conjugation by H.

For a supplied Sylow action frame, the representatives of b and w satisfy
the actual square-displacement identity and its square is nonzero. The
order-four actor is the literal image of the supplied x. This module leaves
the quadratic identity and central pairing to separate extensions.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and printed p.678, equations (1)–(2).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
local notation "J" => pCore 2 H
local notation "D" => commutator J
set_option quotPrecheck false in
local notation "Z" => (center J).subgroupOf D
local notation "V" => J ⧸ D
local notation "W" => D ⧸ Z

/-- Both literal quotients in the core square construction are elementary of order sixteen. -/
public theorem parrott_core_quadratic_quotients (h : ParrottCentralizerHypotheses z) :
    IsElementaryAbelian 2 V ∧ Nat.card V = 16 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W = 16 := by
  obtain ⟨hV, hVcard⟩ := parrott_core_abelianization_structure z h
  obtain ⟨hZmap, _, _, _, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide)
  have hZJcard : Nat.card (center J) = 2 := by
    have hh := card_map_of_injective (K := center J)
      (f := (H).subtype.comp (J).subtype)
      ((H).subtype_injective.comp (J).subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hh
    exact hh.symm
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZJcard
  refine ⟨hV, hVcard, ?_, ?_⟩
  · exact {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := (Group.exponent_quotient_dvd Z).trans
        (IsElementaryAbelian.exponent_dvd_p 2 D) }
  · have hh := (Z).index_mul_card
    change Nat.card W * Nat.card Z = Nat.card D at hh
    rw [hZcard, hDcard] at hh
    omega

/-- The actual square map, with its representative evaluation and the zero
supplied by the given second elementary subgroup. -/
public theorem parrott_core_square_map (h : ParrottCentralizerHypotheses z)
    (e : ParrottSecondElementaryData z) :
    ∃ square : V → W,
      (∀ (j : J) (hj : j ^ 2 ∈ D),
        square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩) ∧
      square 1 = 1 ∧ (∃ v : V, v ≠ 1 ∧ square v = 1) := by
  obtain ⟨_, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 V := (parrott_core_abelianization_structure z h).1
  have hsq (j : J) : j ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D (j ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (QuotientGroup.mk' D j)
  let square := elementarySecondCenterSquare D hUpper.le hsq
  refine ⟨square, fun j hj => elementarySecondCenterSquare_apply D hUpper.le hsq j,
    elementarySecondCenterSquare_one D hUpper.le hsq, ?_⟩
  let a : J := ⟨e.a, e.a_mem_core⟩
  refine ⟨QuotientGroup.mk' D a, ?_, ?_⟩
  · intro ha
    have haD : a ∈ D := (QuotientGroup.eq_one_iff _).mp ha
    exact e.a_not_mem_derived (mem_map_of_mem (J).subtype haD)
  · apply (elementarySecondCenterSquare_eq_one_iff D hUpper.le hsq a).mpr
    have ha2 : a ^ 2 = 1 := Subtype.ext (by
      change e.a ^ 2 = 1
      simpa only [e.a_order] using pow_orderOf_eq_one e.a)
    rw [ha2]
    exact one_mem _


/-- Every square map with the literal evaluation intertwines the two
conjugation actions; this does not depend on how those actions were constructed. -/
public theorem parrott_core_square_equivariant
    (h : ParrottCentralizerHypotheses z)
    (square : V → W)
    (hsquare : ∀ (j : J) (hj : j ^ 2 ∈ D),
      square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩)
    (L : (H ⧸ J) →* MulAut V) (R : (H ⧸ J) →* MulAut W)
    (hL : ∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
      L (QuotientGroup.mk' J a) (QuotientGroup.mk' D d) = QuotientGroup.mk' D d')
    (hR : ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
      R (QuotientGroup.mk' J a) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d') :
    ∀ a v, square (L a v) = R a (square v) := by
  have hsq (j : J) : j ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D (j ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (parrott_core_abelianization_structure z h).1.exponent_dvd_p
      (QuotientGroup.mk' D j)
  intro a v
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective J a
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective D v
  let j' : J := MulAut.conjNormal a j
  have hj' : (j' : H) = a * (j : H) * a⁻¹ := rfl
  rw [hL a j j' hj', hsquare j (hsq j), hsquare j' (hsq j')]
  symm
  apply hR
  change (j' : H) ^ 2 = a * (j : H) ^ 2 * a⁻¹
  rw [hj']
  simp only [pow_two]
  group

set_option synthInstance.maxHeartbeats 40000 in
/-- The marked square displacement holds for every descended right action
and every square map evaluating on actual squares. -/
public theorem ParrottSylowActionData.bw_marked_square
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (square : V → W)
    (hsquare : ∀ (j : J) (hj : j ^ 2 ∈ D),
      square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩)
    (R : (H ⧸ J) →* MulAut W)
    (hR : ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
      R (QuotientGroup.mk' J a) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d') :
    ∃ (x : H) (b : J) (w : D),
      (x : G) = f.x ∧ ((b : H) : G) = n.b ∧ (((w : J) : H) : G) = f.w ∧
      orderOf (QuotientGroup.mk' J x) = 4 ∧
      square (QuotientGroup.mk' D b) =
        R ((QuotientGroup.mk' J x) ^ 2) (QuotientGroup.mk' Z w) * QuotientGroup.mk' Z w ∧
      square (QuotientGroup.mk' D b) ≠ 1 := by
  obtain ⟨x, hx, horder, hb, hw, hbsq, hbnot⟩ := f.bw_square_displacement_inputs h
  obtain ⟨bH, hbJ, hb⟩ := hb
  let b : J := ⟨bH, hbJ⟩
  obtain ⟨wJ, hwD, hw⟩ := hw
  let w : D := ⟨wJ, hwD⟩
  let i := (H).subtype.comp (J).subtype
  have hbval : i b = n.b := hb
  have hsq : b ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D (b ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (parrott_core_abelianization_structure z h).1.exponent_dvd_p
      (QuotientGroup.mk' D b)
  let bs : D := ⟨b ^ 2, hsq⟩
  have hbs : i (bs : J) = n.b ^ 2 := by
    change i (b ^ 2) = n.b ^ 2
    rw [map_pow]
    exact congrArg (fun t : G => t ^ 2) hb
  let w' : D := bs * w
  have hw2 : f.w ^ 2 = 1 := by
    have hElem := (parrott_centralizer_structure z h).2.2.2.2.2.1
    let : IsElementaryAbelian 2 D := hElem
    have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) wJ hwD
    have hh' := congrArg i hh
    change i (wJ ^ 2) = i 1 at hh'
    have hwval : i wJ = f.w := hw
    simpa only [map_pow, map_one, hwval] using hh'
  have hx2inv : (x : G) ^ 2 = ((x : G) ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    change (x : G) ^ 4 = 1
    rw [hx]
    exact f.eq01_x
  have hconj : ((w' : J) : H) = x ^ 2 * ((w : J) : H) * (x ^ 2)⁻¹ := by
    apply (H).subtype_injective
    change i (w' : J) = (x : G) ^ 2 * i (w : J) * ((x : G) ^ 2)⁻¹
    change i ((bs : J) * (w : J)) = _
    rw [map_mul, hbs, hw, hbsq]
    simp only [Tits.parrottCommutator]
    have hwInv : f.w⁻¹ = f.w := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw2)
    simp only [← hx2inv, hwInv]
    calc
      _ = ((x : G) ^ 2 * f.w * (x : G) ^ 2) * (f.w ^ 2) := by
        simp only [pow_two]
        group
      _ = _ := by rw [hw2, mul_one]
  refine ⟨x, b, w, hx, hb, hw, horder, ?_, ?_⟩
  · rw [← map_pow, hR (x ^ 2) w w' hconj, hsquare b hsq]
    change QuotientGroup.mk' Z bs = QuotientGroup.mk' Z (bs * w) * QuotientGroup.mk' Z w
    rw [map_mul, mul_assoc, ← map_mul]
    have hwself : w * w = 1 := by
      apply Subtype.ext
      have hElem := (parrott_centralizer_structure z h).2.2.2.2.2.1
      let : IsElementaryAbelian 2 D := hElem
      change wJ * wJ = 1
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) wJ hwD
    rw [hwself, map_one, mul_one]
  · rw [hsquare b hsq]
    intro hzero
    have hc : b ^ 2 ∈ center J := (QuotientGroup.eq_one_iff (N := Z) (⟨b ^ 2, hsq⟩ : D)).mp hzero
    have hm := mem_map_of_mem i hc
    rw [(parrott_centralizer_structure z h).1] at hm
    apply hbnot
    simpa only [map_pow, hbval] using hm
end Stellmacher.Recognition
