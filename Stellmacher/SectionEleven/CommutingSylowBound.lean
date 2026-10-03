module
public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionNine.LemmaNineOne
public import Stellmacher.SectionNine.LemmaNineTen
public import Stellmacher.SectionTen.AmbientTenOne

/-!
# The Sylow bound for commuting critical centers

For an actual Sylow terminal context, commuting critical centers imply that
its original ambient Sylow subgroup has order at most 2^15. No assumption
that every ambient two-local is solvable is made: both possible odd critical
distances are retained. The native (9.10) bound and (7.5) give distance one
or three. At distance one, (9.1) gives order 2^7; at distance three, the
complete ambient (10.1) gives order at most 2^12 in either alternative.
The inclusion of the generated join identifies its restricted Sylow with
the original subgroup, so this is a bound on the supplied ambient Sylow.

Source: Stellmacher, Theorem 1 and Section Eleven, using (7.5), (9.1),
(9.10), and (10.1), Journal of Algebra 190 (1997).
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven SectionNine
universe u

public theorem commuting_terminal_sylow_card_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥) :
    Nat.card S0 ≤ 2 ^ 15 := by
  have hbound := lemma_nine_ten_ambient (ctx.toSectionNineContext hcomm)
  obtain ⟨half, hodd⟩ :=
    (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath hcomm).odd_distance
  change ctx.criticalPath.length ≤ 3 at hbound
  change ctx.criticalPath.length = 2 * half + 1 at hodd
  have hlength : ctx.criticalPath.length = 1 ∨ ctx.criticalPath.length = 3 := by omega
  rcases hlength with hone | hthree
  · have hcard := (lemma_nine_one_ambient (ctx.toSectionNineContext hcomm) hone).2.2.1
    change Nat.card S0 = 2 ^ 7 at hcard
    rw [hcard]
    norm_num
  · let tenCtx := ctx.toSectionTenContext hcomm hthree
    let middle := ctx.criticalPath.path ⟨2, by omega⟩
    have hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle :=
      ⟨⟨2, by omega⟩, rfl, rfl⟩
    let W := conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    let Wnext := GeneratedNeighborhoodV ctx.Γ middle
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓ Wnext
    have hconclusion := SectionTen.ambient_lemma_ten_one tenCtx middle W W0 Wnext
      hpath rfl rfl rfl
    have hcard : Nat.card ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2)) = Nat.card S0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.sylow_le_join).toEquiv
    cases hconclusion.alternative with
    | a horders _ _ _ _ =>
      rw [hcard] at horders
      exact horders.2.trans (by norm_num)
    | b horders _ _ _ =>
      rw [hcard] at horders
      exact horders.2.trans (by norm_num)

end Stellmacher.SectionEleven
