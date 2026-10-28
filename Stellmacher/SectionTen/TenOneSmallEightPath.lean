module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineSevenGoldschmidtOrbits
/-!
# The eight-edge path used in the small-case final contradiction

In the actual Section Ten graph with first local quotient SL₂(2), extend
the supplied first, middle, and terminal vertices to a nonbacktracking
walk of eight edges. These original three vertices are retained literally.
The result asserts adjacency and no immediate reversal; it does not assert
an unsupported distance-eight or global distinctness condition.

The actual initial-orbit quotients from (9.3), together with the supplied
first quotient, make every vertex cubic. Repeatedly choose a neighbor other
than the preceding vertex. The original critical length-three path already
makes its first and terminal vertices distinct.

This supplies the path (a+1,...,a',...,a+9) in the final paragraph of
Stellmacher (10.1)(a3), printed p.62. Subsequent center arguments use only
its nonbacktracking four-edge subwalks.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

public theorem ten_one_small_exists_eight_path
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G→*H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃path:Fin 9→ctx.Γ.Vertex,
      path 0=ctx.criticalPath.firstStep ∧ path 1=middle ∧ path 2=ctx.criticalPath.a' ∧
      (∀i:Fin 8,ctx.Γ.adjacent (path i.castSucc) (path i.succ)) ∧
      (∀i:Fin 7,path i.castSucc.castSucc≠path i.succ.succ) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hshort : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  have hmodels (v:Γ.Vertex) (hv:IsConjugateVertex Γ cp.a v) :
      QuotientIsModel (GAt Γ v) (QAt Γ v) SL2Two :=
    (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort v hv).1
  have hdegree := (nineSeven_cubic_four_path_transitivity_local
    ctx.toLocalContext.toSectionNineLocalContext hmodel hmodels).1
  obtain ⟨_,hfirst,hterminal,hne⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨four,hfour,hfourne⟩ := goldschmidt_neighbor_other Γ cp.a' middle (hdegree cp.a')
  obtain ⟨five,hfive,hfivene⟩ := goldschmidt_neighbor_other Γ four cp.a' (hdegree four)
  obtain ⟨six,hsix,hsixne⟩ := goldschmidt_neighbor_other Γ five four (hdegree five)
  obtain ⟨seven,hseven,hsevenne⟩ := goldschmidt_neighbor_other Γ six five (hdegree six)
  obtain ⟨eight,height,heightne⟩ := goldschmidt_neighbor_other Γ seven six (hdegree seven)
  obtain ⟨nine,hnine,hninene⟩ := goldschmidt_neighbor_other Γ eight seven (hdegree eight)
  refine ⟨![cp.firstStep,middle,cp.a',four,five,six,seven,eight,nine],rfl,rfl,rfl,?_,?_⟩
  · intro i
    fin_cases i
    · exact Γ.adjacent_symm hfirst
    · exact hterminal
    · exact hfour
    · exact hfive
    · exact hsix
    · exact hseven
    · exact height
    · exact hnine
  · intro i
    fin_cases i
    · exact hne
    · exact hfourne.symm
    · exact hfivene.symm
    · exact hsixne.symm
    · exact hsevenne.symm
    · exact heightne.symm
    · exact hninene.symm

end Stellmacher.SectionTen
