module

public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineSevenCenterLines

/-!
# The post-(9.3) direct product of adjacent centers

At a vertex in the initial critical endpoint's orbit, the centers of any
two distinct neighbors form an internal direct product equal to the middle
center, provided the critical length is greater than one. The theorem uses
(9.3) to obtain the middle center of order four and its SL₂(2) local quotient.
The neighbor-center join and the resulting rank-two geometry give distinct
order-two lines. Their join has order four, and elementary abelianness supplies
commutation.

This is the center splitting used in the opening of (9.8) and in Section Ten.
The ambient context retains Hypothesis Two on H and the graph on its embedded
group G. Source: B. Stellmacher, Journal of Algebra 190 (1997), the
direct-product consequence after (9.3), used on printed p.55 in (9.8).
The local refs/latex/stellmacher-n-group.tex abridges this consequence.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative

universe u

public theorem nine_three_center_split
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    {left middle right : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hleft : ctx.Γ.adjacent middle left)
    (hright : ctx.Γ.adjacent middle right)
    (hdistinct : left ≠ right) :
    IsInternalDirectProductTwo (ZAt ctx.Γ middle) (ZAt ctx.Γ left) (ZAt ctx.Γ right) := by
  obtain ⟨hmodel, hcard⟩ := lemma_nine_three_ambient ctx hb middle hmiddle
  obtain ⟨hjoin, hcenters⟩ := nine_seven_center_join ctx middle hmiddle
  have hleftMem := (mem_neighborhood_iff_adjacent ctx.Γ).mpr hleft
  have hrightMem := (mem_neighborhood_iff_adjacent ctx.Γ).mpr hright
  obtain ⟨hlines, _, hdisjoint⟩ := nine_seven_center_lines_of_center_join
    ctx.sectionSeven ctx.Γ middle hmodel hcard hjoin hcenters
  obtain ⟨hleftCard, hleftLe⟩ := hlines left hleftMem
  obtain ⟨hrightCard, hrightLe⟩ := hlines right hrightMem
  have hne := nine_seven_rank_two_neighbor_centers_distinct ctx.sectionSeven ctx.Γ
    hmodel (hjoin ▸ hcard) hleftCard hleft hright hdistinct
  have hsum : ZAt ctx.Γ left ⊔ ZAt ctx.Γ right ≤ ZAt ctx.Γ middle :=
    sup_le hleftLe hrightLe
  have hproper : ZAt ctx.Γ left < ZAt ctx.Γ left ⊔ ZAt ctx.Γ right := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    have hrightLeft : ZAt ctx.Γ right ≤ ZAt ctx.Γ left := heq ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hrightLeft (by omega)).symm
  have hlt : Nat.card (ZAt ctx.Γ left) <
      Nat.card (ZAt ctx.Γ left ⊔ ZAt ctx.Γ right : Subgroup G) := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hproper.le)
    intro heq
    exact hproper.ne (Subgroup.eq_of_le_of_card_ge hproper.le heq.ge)
  have hdvd := Subgroup.card_dvd_of_le hsum
  rw [hcard] at hdvd
  obtain ⟨power, hpower, hsumCard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (ZAt ctx.Γ left ⊔ ZAt ctx.Γ right : Subgroup G) ∣ 2 ^ 2 from hdvd)
  have hsumFour : Nat.card (ZAt ctx.Γ left ⊔ ZAt ctx.Γ right : Subgroup G) = 4 := by
    interval_cases power <;> simp_all
  refine ⟨(Subgroup.eq_of_le_of_card_ge hsum (by omega)).symm,
    hdisjoint left right hleftMem hrightMem hdistinct, ?_⟩
  let _ : IsElementaryAbelian 2 (ZAt ctx.Γ middle) :=
    z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hleftMem
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm
    (⟨x, hleftLe hx⟩ : ZAt ctx.Γ middle) (⟨y, hrightLe hy⟩ : ZAt ctx.Γ middle))

end Stellmacher.SectionNine
