module
public import Stellmacher.SectionTen.TenOneLargeSylowCard
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex
public import Stellmacher.SectionTen.TenOneLargeTerminalCoreBound

/-!
# The large-case bounds for the distinguished Sylow subgroup

In the actual no-transvection Section Ten configuration, the original graph
Sylow subgroup T has order between 2^11 and 2^12. No replacement Sylow,
quotient model or additional cardinality bound is supplied to the theorem.

The terminal residual core has order512, from its module of order32 and its
quotient of order16. The proved terminal core-index bound makes Q_terminal
have order between512 and1024. A middle-stabilizer conjugation preserves the
cardinality of the first and terminal cores. The actual initial-edge Sylow
data realizes T as a Sylow subgroup of the first stabilizer. Its image in
the proved Frobenius20 quotient has order4; the exact quotient kernel gives
|T|=4|Q_first|. Combining these identities yields the stated interval.

Source: Stellmacher (10.1)(b), Journal of Algebra 190 (1997), printed pp.60,65,
using the source-(18) and source-(19) structure and the final core-index bound.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem large_sylow_card_bounds_of_core_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hindex : (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')).relIndex
      (QAt ctx.Γ ctx.criticalPath.a')≤2) :
    2^11≤Nat.card T ∧ Nat.card T≤2^12 := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let Q:=QAt ctx.Γ ctx.criticalPath.firstStep
  let Qe:=QAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  have hUQ : U≤Qe:=by
    change twoCoreIn (ctx.Γ.twoResidualAt _)≤ctx.Γ.twoCoreAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVcard : Nat.card V=32:=(ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hUcard : Nat.card U=512:=by
    have hh : Nat.card U=16*Nat.card V:=ten_one_large_residual_quotient_card ctx middle hpath hno
    rw [hVcard] at hh
    exact hh
  have hQlower : 512≤Nat.card Qe:=hUcard ▸ Subgroup.card_le_of_le hUQ
  have hQupper : Nat.card Qe≤1024:=by
    have hh:=(U.subgroupOf Qe).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv,hUcard] at hh
    change U.relIndex Qe*512=Nat.card Qe at hh
    change U.relIndex Qe≤2 at hindex
    omega
  have hQcards : Nat.card Q=Nat.card Qe:=by
    obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
    obtain ⟨mover,hmove⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    have hQmap : Qe.map (MulAut.conj (mover:G)⁻¹).toMonoidHom=Q:=by
      change (q ctx.Γ ctx.criticalPath.a').map _=q ctx.Γ ctx.criticalPath.firstStep
      rw [←q_act,hmove]
    rw [←hQmap]
    exact Subgroup.card_map_of_injective (MulAut.conj (mover:G)⁻¹).injective
  have hTcard : Nat.card T = 4 * Nat.card Q :=
    ten_one_large_sylow_card ctx middle hpath hno
  rw [hTcard,hQcards]
  norm_num
  omega

public theorem ten_one_large_sylow_card_bounds
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    : 2^11≤Nat.card T ∧ Nat.card T≤2^12 := by
  exact large_sylow_card_bounds_of_core_index ctx middle hpath hno
    (ten_one_large_terminal_core_index_le_two ctx middle hpath hno)

end Stellmacher.SectionTen
