module
public import Stellmacher.SectionTen.TenOneSmallTerminalCenterFusionExclusion
public import Stellmacher.SectionTen.TenOneSmallInvolutionConjugacy

/-!
# Terminal-center fusion inside a small point centralizer

In the actual small Section Ten context, assume that the full ambient
centralizer of every Wstar point outside the middle center lies in the
mapped middle stabilizer. If a native element commutes with such a point
and its embedded cyclic subgroup is ambient-conjugate to the mapped
terminal center, then it lies in the middle center. The original graph,
ambient group and embedding are retained in the statement.

The conjugate terminal line has order two. Its exact cardinal, transported
through the injective embedding, makes the supplied native element an
involution. Centralizer containment puts it in the middle stabilizer.
If it lies outside the middle center, the proved native involution
reduction conjugates it into Wstar outside that center. Mapping this same
conjugator through the embedding preserves the literal ambient line class.
The completed terminal-class exclusion at the new point, with the same
functional centralizer hypothesis, gives a contradiction.

Source: Stellmacher (10.1)(a3)(11), Journal of Algebra190 (1997), printed
p.62. The final nonsolvable-centralizer assembly supplies the functional
centralizer containment from its contrary solvability assumption.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G→*H} {T A B : Subgroup G}

public theorem ten_one_small_terminal_center_fusion
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ centralizer (W0:Set G)
    (∀a:G,a∈Wstar→a∉ZAt ctx.Γ middle→
      centralizer ({embedding a}:Set H)≤(GAt ctx.Γ middle).map embedding) →
    ∀a v:G,a∈Wstar→a∉ZAt ctx.Γ middle→Commute a v→
      (∃g:H,((ZAt ctx.Γ ctx.criticalPath.a').map embedding).map
        (MulAut.conj g).toMonoidHom=zpowers (embedding v))→v∈ZAt ctx.Γ middle := by
  dsimp only
  intro hcontain a v haW haZ hav hclass
  have hreduce := ten_one_small_commuting_involution_conjugate_wstar ctx middle hpath hsmall hmodel
  by_contra hvZ
  have hvP : v∈GAt ctx.Γ middle := by
    have hh := hcontain a haW haZ
      (mem_centralizer_singleton_iff.mpr (show embedding v*embedding a=embedding a*embedding v from
        by simpa only [map_mul] using congrArg embedding hav.symm.eq))
    obtain ⟨w,hw,heq⟩ := hh
    exact (ctx.embedding_injective heq) ▸ hw
  obtain ⟨actor,hactor⟩ := hclass
  obtain ⟨align,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hterminalCard := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext (by rw [ctx.critical_length]; decide)
      ctx.criticalPath.a' ⟨align,halign⟩).1
  have hvCard : Nat.card (zpowers (embedding v))=2 := by
    rw [←hactor,card_map_of_injective (MulAut.conj actor).injective,
      card_map_of_injective ctx.embedding_injective]
    exact hterminalCard
  have hv2 : orderOf v=2 := by
    rw [Nat.card_zpowers,orderOf_injective embedding ctx.embedding_injective] at hvCard
    exact hvCard
  obtain ⟨g,hgW,hgZ⟩ := hreduce a v haW haZ hv2 hvP hav hvZ
  apply ten_one_small_point_not_conjugate_terminal_center ctx middle hpath hsmall hmodel
    (MulAut.conj g v) hgW.1 hgZ (hcontain _ hgW hgZ)
  refine ⟨embedding g*actor,?_⟩
  have hcomp : (MulAut.conj (embedding g*actor)).toMonoidHom=
      (MulAut.conj (embedding g)).toMonoidHom.comp (MulAut.conj actor).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [hcomp,←map_map,hactor,MonoidHom.map_zpowers]
  apply congrArg zpowers
  simp

end Stellmacher.SectionTen
