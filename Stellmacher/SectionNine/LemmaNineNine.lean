module
public import Stellmacher.SectionNine.NineNineFinalIndex
public import Stellmacher.SectionNine.NineNineLargeIntersection
public import Stellmacher.SectionNine.NineNinePenultimateIntersectionCore
public import Stellmacher.SectionNine.NineNineFinalSupportCommutator
public import Stellmacher.SectionNine.NineNineReversedContainment
public import Stellmacher.SectionNine.LemmaNineEight

/-!
# Stellmacher (9.9): first-center containment bounds the critical distance

In the ambient Section Nine setting, if the first-step center lies in the
terminal module, the critical length is at most three. The original public
statement follows through the existing ambient-context adapter.

Assume a longer path. Actual (9.8), normalized at a genuine reversed critical
pair, puts the terminal module in the first core. The selected canonical
rank-one support gives source (1), and actual (9.7) gives the preceding
module-intersection index at least four. The extraction and supplied-path
(9.5) classification yield the terminal order-thirty-two wreath case.
Its literal quotient action places the first center in the terminal
intersection, supplies the centralizing neighbor conjugator, and identifies
the actual normalizer edge index three. The finite two-group index argument
then makes the preceding penultimate intersection have index two. The proved
core containment and support commutator bound put it inside the original
intersection, contradicting the index-four lower bound.

Every geometric witness, quotient action, center line, and normalizer is
produced from the original context. Source: Stellmacher, Journal of Algebra
190 (1997), (9.9), printed pp.56--57/PDF pp.46--47 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The ambient-retaining form of Stellmacher (9.9). -/
public theorem lemma_nine_nine_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.a') :
    ctx.criticalPath.length ≤ 3 := by
  by_contra! hb
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hshort : 1<cp.length := by change 3<cp.length at hb; omega
  have hcore := nine_nine_terminal_core_of_eight_bound lemma_nine_eight_ambient ctx hb hcontain
  have hmodel := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).1
  obtain ⟨previous,hpreviousAdj,hne⟩ := goldschmidt_neighbor_other Γ cp.a cp.firstStep
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel).degree
  have hprevious := (mem_neighborhood_iff_adjacent Γ).mpr hpreviousAdj
  have hlarge := nine_nine_previous_intersection_index_ge_four ctx hb previous hprevious hne
  obtain ⟨support,hsupport,hcomm,hcontrol⟩ := nine_nine_support_of_terminal_core ctx hshort hcore
  let data : NineNineSupportData ctx.toLocalContext hb := {
    terminal_core := hcore
    support := support
    support_le := hsupport
    support_commutator := hcomm
    centralizer_commutator := hcontrol
    previous := previous
    previous_neighbor := hprevious
    previous_ne := hne
    maximal_eq := nine_nine_maximal_eq_intersection ctx hb support (hsupport.trans hcore)
      hcomm previous hprevious hne
    large_index := hlarge }
  exact nine_nine_support_index_contradiction ctx.toLocalContext hb data
    (nine_nine_final_index_two lemma_nine_eight_ambient ctx hb hcore previous hprevious hne hlarge)
    (nine_nine_penultimate_intersection_le_core lemma_nine_eight_ambient ctx hb hcore
      previous hprevious hne hlarge)
    (nine_nine_final_support_commutator ctx hb hcore previous hprevious hne hlarge
      support hsupport hcontrol)

/-- **Stellmacher (9.9).** First-center containment forces critical distance at most three. -/
public theorem lemma_nine_nine
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.a') :
    ctx.criticalPath.length ≤ 3 :=
  lemma_nine_nine_ambient ctx.toAmbientContext hcontain

end Stellmacher.SectionNine
