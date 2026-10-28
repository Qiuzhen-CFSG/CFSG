module

public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Small dual offenders give a quadratic ratio bound

If an elementary actor has fixed codimension at most two on the dual, any
nonidentity element gives a cyclic quadratic actor on the original module.
The fixed codimension of a cyclic actor is unchanged by duality. In
particular every dual offender of rank at most two gives the required bound.

This is used in the alternating natural branches of Aschbacher–Smith B.5.13,
printed pp.110–112, to reduce to offenders of rank at least three.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem quadraticRatio_le_two_of_dual_fixedCodim_le_two {A : Subgroup G}
    (hA : IsElementaryTwo A) (hd : fixedCodim ρ.dual A ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  obtain ⟨a, ha, hne⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! h
    exact hA.1 (eq_bot_iff.mpr fun a ha => h a ha)
  let : IsElementaryAbelian 2 A := hA.2
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have ho : orderOf a = 2 := orderOf_eq_prime ha2 hne
  obtain ⟨hb, hr, hq, _⟩ := involution_actor_rank_and_fixedCodim ρ a ho
  have hs : fixedSpace ρ.dual A ≤ fixedSpace ρ.dual (zpowers a) := by
    intro v hv g
    exact hv ⟨g, (zpowers_le.mpr ha) g.property⟩
  have hm := Submodule.finrank_mono hs
  have hdA := fixedCodim_add_finrank ρ.dual A
  have hda := fixedCodim_add_finrank ρ.dual (zpowers a)
  rw [fixedCodim_zpowers_dual] at hda
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨zpowers a, hb, hq, ?_⟩
  omega

theorem quadraticRatio_le_two_of_small_dual_offender {A : Subgroup G}
    (hA : IsOffender ρ.dual A) (hr : rank A ≤ 2) : quadraticRatio ρ ≤ 2 :=
  quadraticRatio_le_two_of_dual_fixedCodim_le_two ρ hA.1 (hA.2.trans hr)

end Representation.BinaryOffender
