module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterRank
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank

/-!
# Excluding the Higman--Sims quotient from the original elementary subgroup

The elementary subgroup of order 64 and the native quotient rank bound
force the two-primary covering kernel to have order at least four. This
contradicts the proved two-primary HS multiplier bound.

Source: Aschbacher--Smith, I.1.3(1) and 12.7.5, printed pp.407,840.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section07

/-- The original elementary 64 excludes the HS alternative without any
centrality premise on the marked field point. -/
theorem original_point_ordinary_not_hs
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (U : Subgroup B) [IsElementaryAbelian 2 U] (hU : Nat.card U = 64)
    (hp : IsPGroup 2 (center B))
    (e : B ⧸ center B ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 f.ker := hker ▸ hp
  have hbig : 4 ≤ Nat.card f.ker :=
    (original_point_four_le_card_kernel U hU f Sporadic.LeechRelated.HS.twoRank_le_four).trans
      (card_le_of_le inf_le_right)
  have hnot := Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.not_four_dvd_card_kernel
    f hf hker.le hk
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  rw [hn] at hbig
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n ≤ 1 := by omega
    have hsmall := pow_le_pow_right' (by decide : 1 ≤ 2) hn1
    norm_num at hsmall
    omega
  apply hnot
  rw [hn]
  exact pow_dvd_pow 2 hn2

end CFSG.Quasithin.Chapter12.Section07
