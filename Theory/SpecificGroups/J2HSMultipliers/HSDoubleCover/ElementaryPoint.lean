module

public import Theory.SpecificGroups.J2HSMultipliers.HSDoubleCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementaryFixedPoint

/-!
# Fixed letters for elementary subgroups of the HS double cover

A square-one element of the literal double cover cannot project to a
fixed-point-free involution: all such degree-100 permutations are conjugate
in the alternating group, and their lifts square to the nonidentity sign.
The common-fixed-letter theorem for HS then applies to the projected image
of an elementary subgroup whenever that image has order greater than eight.
Both maps remain the projections of the original pullback cover.

Source: GLS3 Proposition 5.2.4(e), via the existing HS double-cover
construction; used in the HS case of Aschbacher--Smith 12.6.12, pp.825--826.
-/

public section

open Subgroup GLS3.Chapter5.SchurPresentation
namespace Theory.SpecificGroups.J2HSMultipliers.HS
open Sporadic.LeechRelated.HS
attribute [local irreducible] involution
variable [Group.IsPerfect Carrier]

/-- An involution upstairs cannot project to a fixed-point-free permutation. -/
theorem square_one_projection_has_fixed_point (x : DoubleCover) (hx : x ^ 2 = 1) :
    ∃ p : Fin 100, (projection x : Equiv.Perm (Fin 100)) p = p := by
  classical
  by_contra hn
  have hsupp : (projection x : Equiv.Perm (Fin 100)).support.card = 100 := by
    have hh : (projection x : Equiv.Perm (Fin 100)).support = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact Equiv.Perm.mem_support.mpr (fun hp => hn ⟨p,hp⟩)
    rw [hh,Finset.card_univ,Fintype.card_fin]
  obtain ⟨y,hy,hy2⟩ := exists_alternating_lift_square
  have hconj : IsConj (alternatingInclusion involution) (alternatingInclusion (projection x)) := by
    apply alternating_involution_isConj_of_card_support_eq
    · change inclusion involution ^ 2 = 1
      rw [←map_pow,involution_square,map_one]
    · change inclusion (projection x) ^ 2 = 1
      rw [←map_pow,←map_pow,hx,map_one,map_one]
    · intro he
      have hh := congrArg (fun z : alternatingGroup (Fin 100) => z.val 0) he
      exact involution_fixedPointFree 0 hh
    · change (involution : Equiv.Perm (Fin 100)).support.card =
        (projection x : Equiv.Perm (Fin 100)).support.card
      rw [involution_support_card,hsupp]
  obtain ⟨c,hc⟩ := isConj_iff.mp hconj
  have heq := DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
    (schurAlternatingCovering 95) (natCard_ker_schurAlternatingCovering 95)
    (x := y) (y := toAlternatingCover x) (c := c) (by
      change schurAlternatingProjection 95 y ^ 2 = 1
      rw [hy,←map_pow,involution_square,map_one]) (by
      change c * schurAlternatingProjection 95 y * c⁻¹ =
        schurAlternatingProjection 95 (toAlternatingCover x)
      rw [hy]
      exact hc.trans (DFunLike.congr_fun projection_square x).symm)
  have hx2 : toAlternatingCover x ^ 2 = 1 := by rw [←map_pow,hx,map_one]
  exact schurAlternatingCentral_ne_one 95 (hy2.symm.trans (heq.trans hx2))

end Theory.SpecificGroups.J2HSMultipliers.HS

namespace Theory.SpecificGroups.J2HSMultipliers.HS
open Subgroup Sporadic.LeechRelated.HS
variable [Group.IsPerfect Carrier]

/-- The common fixed point for the literal projection of a large elementary
subgroup of the double cover. -/
theorem elementary_projection_common_fixed_point (U : Subgroup DoubleCover)
    [IsElementaryAbelian 2 U] (hcard : 8 < Nat.card (U.map projection)) :
    ∃ p : Fin 100, ∀ x ∈ U,
      (projection x : Equiv.Perm (Fin 100)) p = p := by
  let : IsElementaryAbelian 2 (U.map projection) := IsElementaryAbelian.map projection
  obtain ⟨p,hp⟩ := LiftedElementaryPoint.common_fixed_point (U.map projection) hcard (by
    rintro w ⟨x,hx,rfl⟩
    exact square_one_projection_has_fixed_point x (elemPow_eq_one_of_isElementaryAbelian x hx))
  exact ⟨p,fun x hx => hp _ (mem_map_of_mem projection hx)⟩
end Theory.SpecificGroups.J2HSMultipliers.HS
