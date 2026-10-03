module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticCount

namespace SmallNonabelianTwoGroup

public theorem not_five_dvd_quadratic_preserving_actor_card
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
    (hsingular : ∀ vector ∈ singular, square vector = 1)
    (actor : Subgroup (MulAut V))
    (hinvariant : ∀ aut ∈ actor, ∀ vector, square (aut vector) = square vector) :
    ¬ 5 ∣ Nat.card actor := by
  intro hfive
  have hmod := invariant_fiber_card_mod_five_of_five_dvd_actor
    hV square hone actor hinvariant hfive
  have hnot := quadratic_zero_count_not_one_mod_five hV hW square polar hone
    hquadratic hbilinear hnonzero singular hsingularCard hsingular
  exact hnot hmod

end SmallNonabelianTwoGroup

