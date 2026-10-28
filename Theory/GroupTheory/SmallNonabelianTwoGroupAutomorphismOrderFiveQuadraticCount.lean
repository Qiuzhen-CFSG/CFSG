module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticCountTransport
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticCountCoordinates

namespace SmallNonabelianTwoGroup

public theorem quadratic_zero_count_not_one_mod_five
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 2)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ left right,
      square (left * right) = square left * square right * polar left right)
    (hbilinear : ∀ left right other,
      polar (left * right) other = polar left other * polar right other)
    (hnonzero : ∃ left right, polar left right ≠ 1)
    (singular : Subgroup V) (hsingularCard : 4 ≤ Nat.card singular)
    (hsingular : ∀ vector ∈ singular, square vector = 1) :
    Nat.card {vector : V // square vector = 1} % 5 ≠ 1 := by
  obtain ⟨coordinateSquare, coordinatePolar, coordinateSingular, hzero,
    hquadratic', hbilinear', hnonzero', hsingularCard', hsingular', hcount⟩ :=
    exists_quadratic_coordinate_model hV hW square polar hone hquadratic hbilinear
      hnonzero singular hsingularCard hsingular
  rw [hcount]
  exact quadratic_coordinate_zero_count_not_one_mod_five coordinateSquare coordinatePolar
    hzero hquadratic' hbilinear' hnonzero' coordinateSingular hsingularCard' hsingular'

end SmallNonabelianTwoGroup

