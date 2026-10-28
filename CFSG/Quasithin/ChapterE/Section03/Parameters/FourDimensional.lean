module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.FourDimensionalRatio

/-!
# The minimum involution displacement in a non-FF four-space

An involution is quadratic in characteristic two, and its displacement has
dimension at most half the module dimension. Absence of FF offenders forces
that dimension to be at least two. A finite quadratic ratio supplies an actual
involution, so the minimum displacement is two.

Source application: Aschbacher--Smith, 15.2.14(6), printed p.1112. This argument
uses the four-dimensional chosen module before the proper-support exclusion.
-/

public section

namespace CFSG.Quasithin.ChapterE

open Subgroup Representation.BinaryOffender

variable {X W : Type*} [Group X] [Finite X] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Every involution on a non-FF binary four-space has displacement two. -/
theorem involution_fixedCodim_eq_two_of_four_nonFF
    (ρ : Representation (ZMod 2) X W)
    (hdim : Module.finrank (ZMod 2) W ≤ 4) (hn : ¬ IsFFModule ρ)
    (t : X) (ht : orderOf t = 2) : fixedCodim ρ (zpowers t) = 2 := by
  obtain ⟨hA, _, hquad, _⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  exact (quadratic_actor_four_of_no_ff ρ hdim hn hA hquad).2

omit [FiniteDimensional (ZMod 2) W] in
/-- A finite quadratic ratio supplies an actual involution in the actor. -/
theorem exists_involution_of_quadraticRatio_le_two
    (ρ : Representation (ZMod 2) X W) (hq : quadraticRatio ρ ≤ 2) :
    ∃ t : X, orderOf t = 2 := by
  obtain ⟨A, hA, _, _⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  let := hA.2
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hA.1
  refine ⟨a, orderOf_eq_prime ?_ ?_⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (a : X) a.property
  · exact fun he => ha (Subtype.ext he)

/-- The parameter `m` equals two on a non-FF four-space with finite ratio. -/
theorem moduleM_eq_two_of_four_nonFF
    (ρ : Representation (ZMod 2) X W)
    (hdim : Module.finrank (ZMod 2) W ≤ 4) (hn : ¬ IsFFModule ρ)
    (hq : quadraticRatio ρ ≤ 2) : moduleM ρ = 2 := by
  obtain ⟨t, ht, hm⟩ := moduleM_attained ρ
    (exists_involution_of_quadraticRatio_le_two ρ hq)
  exact hm.symm.trans (involution_fixedCodim_eq_two_of_four_nonFF ρ hdim hn t ht)

end CFSG.Quasithin.ChapterE
