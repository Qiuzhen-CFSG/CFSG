module

public import Theory.Mathieu.SmallModuleRanks.CommutingCover
public import Theory.Mathieu.SmallModuleRanks.M24Certificate
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Intrinsic two-rank of M₂₄

The 64-part noncommuting cover bounds elementary subgroups of the
literal order-1024 candidate by 64. Its previously certified order and
that of M₂₄ identify it as Sylow. The elementary-cardinality criterion
then gives the rank bound for the original Witt-design group.

Source: Aschbacher--Smith, G.7.3(2), printed p.348; rank references p.347.
-/

public section
namespace Sporadic.Mathieu
open M24LocalGeometry.SylowNormalizer
open M24LocalGeometry.SylowNormalizer.OrderEnumeration
open SmallModuleRanks SmallModuleRanks.M24Certificate

/-- Every elementary subgroup of the marked M₂₄ Sylow group has order at most 64. -/
theorem m24_sylow_elementary_card_le_sixtyFour (E : Subgroup candidate)
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 64 := by
  apply elementary_card_le_of_commuting_cover (fun c a => element (bucket c a)) ?_ ?_ E hE
  · intro g hg
    obtain ⟨i, rfl⟩ := element_surjective g
    have hs (x : Fin 24) : point i (point i x) = x := by
      have he := congrArg (fun z : candidate => z.val.val x) hg
      simpa only [pow_two, Subgroup.coe_mul, Equiv.Perm.mul_apply,
        element_apply, Subgroup.coe_one, Equiv.Perm.one_apply] using he
    exact ⟨(slot i).1, (slot i).2,
      congrArg element (square_cover i (hs (squareWitness i)))⟩
  · intro c a b hab
    rcases commuting_unique c a b with he | ⟨x, hx⟩
    · exact congrArg element he
    · apply False.elim
      apply hx
      have he := congrArg (fun z : candidate => z.val.val x) hab
      simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, element_apply] using he

/-- The native simple M₂₄ has two-rank at most six. -/
theorem m24_twoRank_le_six : primeRank 2 M24 ≤ 6 := by
  let P : Sylow 2 M24 := Sylow.ofCard candidate (by
    rw [candidate_card, m24_order]
    decide +kernel)
  rw [P.primeRank_eq]
  change primeRank 2 candidate ≤ 6
  apply (primeRank_le_iff_elementary_card_le _).mpr
  exact m24_sylow_elementary_card_le_sixtyFour

end Sporadic.Mathieu
