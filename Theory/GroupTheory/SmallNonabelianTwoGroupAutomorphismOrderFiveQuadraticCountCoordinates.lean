module

public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

namespace SmallNonabelianTwoGroup
namespace CountCoordinates

private abbrev Space := Fin 4 → ZMod 2

private def polynomial (coeff : Fin 10 → ZMod 2) (vector : Space) : ZMod 2 :=
  coeff 0 * vector 0 + coeff 1 * vector 1 +
  coeff 2 * vector 2 + coeff 3 * vector 3 +
  coeff 4 * vector 0 * vector 1 + coeff 5 * vector 0 * vector 2 +
  coeff 6 * vector 0 * vector 3 + coeff 7 * vector 1 * vector 2 +
  coeff 8 * vector 1 * vector 3 + coeff 9 * vector 2 * vector 3

private theorem representation
    (square : Space → ZMod 2) (polar : Space → Space → ZMod 2)
    (hzero : square 0 = 0)
    (hquadratic : ∀ left right,
      square (left + right) = square left + square right + polar left right)
    (hbilinear : ∀ left right other,
      polar (left + right) other = polar left other + polar right other) :
    ∃ coeff : Fin 10 → ZMod 2, square = polynomial coeff := by
  let basis : Fin 4 → Space := fun index => Pi.single index 1
  let coeff : Fin 10 → ZMod 2 :=
    ![square (basis 0), square (basis 1), square (basis 2), square (basis 3),
      polar (basis 0) (basis 1), polar (basis 0) (basis 2),
      polar (basis 0) (basis 3), polar (basis 1) (basis 2),
      polar (basis 1) (basis 3), polar (basis 2) (basis 3)]
  have hleft (vector : Space) : polar 0 vector = 0 := by
    have equation := hquadratic 0 vector
    simpa [hzero] using equation.symm
  have hright (vector : Space) : polar vector 0 = 0 := by
    have equation := hquadratic vector 0
    simpa [hzero] using equation.symm
  have binary : ∀ scalar : ZMod 2, scalar = 0 ∨ scalar = 1 := by decide
  have hscale (scalar : ZMod 2) (vector : Space) :
      square (scalar • vector) = scalar * square vector := by
    rcases binary scalar with rfl | rfl <;> simp [hzero]
  have hscalePolar (leftScalar rightScalar : ZMod 2) (left right : Space) :
      polar (leftScalar • left) (rightScalar • right) =
        leftScalar * rightScalar * polar left right := by
    rcases binary leftScalar with rfl | rfl <;>
      rcases binary rightScalar with rfl | rfl <;> simp [hleft, hright]
  refine ⟨coeff, ?_⟩
  funext vector
  have hdecomp : vector =
      ((vector 0 • basis 0 + vector 1 • basis 1) + vector 2 • basis 2) +
        vector 3 • basis 3 := by
    ext index
    fin_cases index <;> simp [basis]
  conv_lhs => rw [hdecomp]
  simp only [hquadratic, hbilinear, hscale, hscalePolar]
  dsimp [polynomial, coeff]
  ring

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem enumeration : ∀ coeff : Fin 10 → ZMod 2,
    (Finset.univ.filter fun vector : Space => polynomial coeff vector = 0).card % 5 = 1 →
    (∀ vector, polynomial coeff vector = 0) ∨
      (∀ left right : Space, left ≠ 0 → right ≠ 0 → left ≠ right →
        polynomial coeff left = 0 → polynomial coeff right = 0 →
        polynomial coeff (left + right) ≠ 0) := by
  decide +kernel

private theorem singular_pair (singular : AddSubgroup Space)
    (hsingularCard : 4 ≤ Nat.card singular) :
    ∃ left ∈ singular, ∃ right ∈ singular,
      left ≠ 0 ∧ right ≠ 0 ∧ left ≠ right := by
  have hthree : 2 < (singular : Set Space).ncard := by
    change 2 < Nat.card singular
    omega
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hfirstSecond,
    hfirstThird, hsecondThird⟩ :=
      (Set.two_lt_ncard_iff (s := (singular : Set Space))).mp hthree
  refine ⟨first - second, singular.sub_mem hfirst hsecond,
    first - third, singular.sub_mem hfirst hthird,
    sub_ne_zero.mpr hfirstSecond, sub_ne_zero.mpr hfirstThird, ?_⟩
  simpa only [ne_eq, sub_right_inj] using hsecondThird

end CountCoordinates

public theorem quadratic_coordinate_zero_count_not_one_mod_five
    (square : (Fin 4 → ZMod 2) → ZMod 2)
    (polar : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → ZMod 2)
    (hzero : square 0 = 0)
    (hquadratic : ∀ left right,
      square (left + right) = square left + square right + polar left right)
    (hbilinear : ∀ left right other,
      polar (left + right) other = polar left other + polar right other)
    (hnonzero : ∃ left right, polar left right ≠ 0)
    (singular : AddSubgroup (Fin 4 → ZMod 2)) (hsingularCard : 4 ≤ Nat.card singular)
    (hsingular : ∀ vector ∈ singular, square vector = 0) :
    Nat.card {vector : Fin 4 → ZMod 2 // square vector = 0} % 5 ≠ 1 := by
  classical
  obtain ⟨coeff, hsquare⟩ :=
    CountCoordinates.representation square polar hzero hquadratic hbilinear
  intro hmod
  rw [hsquare, Nat.card_eq_fintype_card, Fintype.card_subtype] at hmod
  rcases CountCoordinates.enumeration coeff hmod with hvanish | helliptic
  · obtain ⟨left, right, hpair⟩ := hnonzero
    apply hpair
    have hvanishSquare (vector) : square vector = 0 := by
      rw [hsquare]
      exact hvanish vector
    have equation := hquadratic left right
    simpa only [hvanishSquare, zero_add] using equation.symm
  · obtain ⟨left, hleft, right, hright, hleftZero, hrightZero, hdistinct⟩ :=
      CountCoordinates.singular_pair singular hsingularCard
    apply helliptic left right hleftZero hrightZero hdistinct
    · rw [← hsquare]
      exact hsingular left hleft
    · rw [← hsquare]
      exact hsingular right hright
    · rw [← hsquare]
      exact hsingular (left + right) (singular.add_mem hleft hright)


end SmallNonabelianTwoGroup
