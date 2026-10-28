module
public import Stellmacher.SectionTen.TenOneSmallCentralizerElementary

/-!
# Move a small commuting pair into the terminal edge

For the actual small Section Ten context, a native involution in the
middle stabilizer can be conjugated into the terminal edge by a member
of that same stabilizer. If it commutes with a supplied Wstar point and
both points lie outside the middle center, one such conjugator preserves
all these data: the Wstar membership, both center exclusions, involution
order, and commutation. The original ambient embedding and graph are fixed.

By (7.3), a Sylow two-subgroup of the terminal edge is Sylow in the middle
stabilizer. Put the involution's cyclic subgroup into a Sylow subgroup of
that stabilizer and conjugate the two Sylows. The proved normalization of
Wstar and the native center covariance preserve the other point and both
center exclusions under exactly this conjugator.

This is the first stage of the native involution reduction in Stellmacher
(10.1)(a3)(11), Journal of Algebra190 (1997), printed p.62. Later edge and
terminal-residual lemmas act on this retained conjugated pair.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped Pointwise
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G→*H} {T A B : Subgroup G}

public theorem ten_one_small_involution_edge_normalization
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a v:G) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ centralizer (W0:Set G)
    a∈Wstar→a∉ZAt ctx.Γ middle→ orderOf v=2→v∈GAt ctx.Γ middle→
      Commute a v→v∉ZAt ctx.Γ middle→
      ∃g:G,g∈GAt ctx.Γ middle ∧
        MulAut.conj g v∈GAt ctx.Γ middle⊓GAt ctx.Γ ctx.criticalPath.a' ∧
        MulAut.conj g a∈Wstar ∧ MulAut.conj g a∉ZAt ctx.Γ middle ∧
        MulAut.conj g v∉ZAt ctx.Γ middle ∧ orderOf (MulAut.conj g v)=2 ∧
        Commute (MulAut.conj g a) (MulAut.conj g v) := by
  dsimp only
  intro haW haZ hv2 hvP hav hvZ
  let Γ := ctx.Γ
  let P := GAt Γ middle
  let edge := P⊓GAt Γ ctx.criticalPath.a'
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ GeneratedNeighborhoodV Γ middle
  let Wstar := QAt Γ middle⊓centralizer (W0:Set G)
  let ES : Sylow 2 edge := default
  have hadj := (sectionTenOpeningGeometry ctx middle hpath).2.2.1
  obtain ⟨_,SS,hSS⟩ := ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    middle ctx.criticalPath.a' ((mem_neighborhood_iff_adjacent Γ).mpr hadj) ES).1
  have hSterminal : (SS:Subgroup P).map P.subtype≤GAt Γ ctx.criticalPath.a' := by
    rw [hSS]
    exact (map_subtype_le (ES:Subgroup edge)).trans inf_le_right
  let vp : P := ⟨v,hvP⟩
  have hvp2 : vp^2=1 := by
    apply Subtype.ext
    change v^2=1
    simpa only [hv2] using pow_orderOf_eq_one v
  let _ : IsElementaryAbelian 2 (zpowers vp) := IsElementaryAbelian.zpowers_of_pow_eq_one hvp2
  obtain ⟨VS,hVS⟩ := (IsElementaryAbelian.isPGroup 2 (zpowers vp)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P VS SS
  have hmem : MulAut.conj g vp∈(SS:Subgroup P) := by
    rw [←hg]
    change MulAut.conj g vp∈(VS:Subgroup P).map (MulAut.conj g).toMonoidHom
    exact mem_map_of_mem _ (hVS (mem_zpowers vp))
  have hterminal : MulAut.conj (g:G) v∈GAt Γ ctx.criticalPath.a' :=
    hSterminal (mem_map_of_mem P.subtype hmem)
  have hWnorm : P≤normalizer (Wstar:Set G) :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).1
  have hZnorm : P≤normalizer (ZAt Γ middle:Set G) := stabilizer_le_normalizer_z Γ middle
  have hconjW : MulAut.conj (g:G) a∈Wstar :=
    (mem_normalizer_iff.mp (hWnorm g.property) a).mp haW
  have hconjaZ : MulAut.conj (g:G) a∉ZAt Γ middle := by
    intro ha
    exact haZ ((mem_normalizer_iff.mp (hZnorm g.property) a).mpr ha)
  have hconjvZ : MulAut.conj (g:G) v∉ZAt Γ middle := by
    intro hv
    exact hvZ ((mem_normalizer_iff.mp (hZnorm g.property) v).mpr hv)
  refine ⟨g,g.property,⟨?_,hterminal⟩,hconjW,hconjaZ,hconjvZ,?_,?_⟩
  · exact P.mul_mem (P.mul_mem g.property hvP) (P.inv_mem g.property)
  · exact ((MulAut.conj (g:G)).orderOf_eq v).trans hv2
  · exact hav.map (MulAut.conj (g:G)).toMonoidHom

end Stellmacher.SectionTen
