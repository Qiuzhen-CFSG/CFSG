module
public import Stellmacher.SectionTen.GeneratedContext
public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineSevenShiftedIntersections
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineThreeCoreOmega

/-!
# The opening data for Stellmacher Section Ten

In the commuting critical-pair case of length three, the middle vertex at
path offset two has SL₂(2) core quotient and center of order four. Its center
is the internal direct product of the first-step and terminal centers and
is exactly the omega-one center of its two-core. The two neighboring modules
escape each other's two-cores, and the terminal module centralizer lies in
the terminal two-core.

Local transitivity places the middle vertex in the initial orbit, so (9.3)
and its proved center-splitting and core-omega consequences apply. Criticality
gives the first noncontainment; cubic two-arc transitivity interchanges the
two end vertices and gives the reverse noncontainment. Endpoint alignment
transports the proved (7.7)(b) centralizer bound. The ambient corollary pulls
commuting elements back through the injective embedding, keeping Hypothesis
Two on the original ambient group. The legacy context uses its identity
embedding adapter.

Source: Stellmacher, Journal of Algebra 190 (1997), the paragraph immediately
preceding (10.1), printed p.59/PDF p.49 of
`refs/files/stellmacher-n-group.pdf`, and `refs/latex/stellmacher-n-group.tex`.
Both noncontainment signs and the full internal direct-product assertion
follow the journal scan.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

/-- The standing local data preceding Stellmacher (10.1). -/
public structure SectionTenOpeningData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (middle : Γ.Vertex) : Prop where
  quotient_model : QuotientIsModel (GAt Γ middle) (QAt Γ middle) SL2Two
  center_card : Nat.card (ZAt Γ middle) = 4
  center_direct_product : IsInternalDirectProductTwo
    (ZAt Γ middle) (ZAt Γ cp.firstStep) (ZAt Γ cp.a')
  center_omega : ZAt Γ middle = omegaOneCenter (QAt Γ middle)
  first_noncontainment : ¬ VAt Γ cp.firstStep ≤ QAt Γ cp.a'
  terminal_noncontainment : ¬ VAt Γ cp.a' ≤ QAt Γ cp.firstStep
  endpoint_centralizer : Subgroup.centralizer (VAt Γ cp.a' : Set G) ≤ QAt Γ cp.a'

/-- The offset-two vertex lies in the initial orbit and joins the distinct
first-step and terminal vertices. -/
public theorem sectionTenOpeningGeometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    IsConjugateVertex ctx.Γ ctx.criticalPath.a middle ∧
      ctx.Γ.adjacent middle ctx.criticalPath.firstStep ∧
      ctx.Γ.adjacent middle ctx.criticalPath.a' ∧
      ctx.criticalPath.firstStep ≠ ctx.criticalPath.a' := by
  obtain ⟨index, hindex, rfl⟩ := hpath
  have hlen := ctx.critical_length
  have hfirst : ctx.Γ.adjacent (ctx.criticalPath.path index) ctx.criticalPath.firstStep := by
    have hadj := ctx.criticalPath.path_adj ⟨1, by omega⟩
    have heq : (⟨1, by omega⟩ : Fin ctx.criticalPath.length).succ = index := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [heq] at hadj
    change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩)
      (ctx.criticalPath.path index) at hadj
    rw [ctx.criticalPath.path_first] at hadj
    exact ctx.Γ.adjacent_symm hadj
  have hterminal : ctx.Γ.adjacent (ctx.criticalPath.path index) ctx.criticalPath.a' := by
    have hadj := ctx.criticalPath.path_adj ⟨2, by omega⟩
    have hleft : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).castSucc = index :=
      Fin.ext hindex.symm
    have hright : (⟨2, by omega⟩ : Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hleft, hright, ctx.criticalPath.path_end] at hadj
    exact hadj
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.firstStep
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst))
  refine ⟨⟨actor, hactor⟩, hfirst, hterminal, ?_⟩
  intro heq
  have hdist := (adjacent_iff_distance_eq_one ctx.Γ).mp ctx.criticalPath.firstStep_adj
  rw [heq, ctx.criticalPath.endpoint_distance, hlen] at hdist
  omega

private theorem opening_noncontainments
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a' ∧
      ¬ VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  have hfirst : ¬ VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    intro hle
    exact ctx.criticalPath.critical.2
      ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans hle)
  refine ⟨hfirst, ?_⟩
  obtain ⟨horbit, hleft, hright, hne⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hmodel := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb middle horbit).1
  obtain ⟨actor, hactorLeft, _, hactorRight⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven ctx.Γ hleft hright hne hright hleft hne.symm
    ⟨1, ctx.Γ.act_one middle⟩ hmodel
  intro hle
  have hmap := Subgroup.map_mono (f := (MulAut.conj actor⁻¹).toMonoidHom) hle
  change (v ctx.Γ ctx.criticalPath.a').map _ ≤
    (q ctx.Γ ctx.criticalPath.firstStep).map _ at hmap
  rw [← v_act, ← q_act, hactorRight, hactorLeft] at hmap
  exact hfirst hmap

private theorem opening_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B) :
    Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ≤
      QAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨actor, _, hactor⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  exact nine_three_module_centralizer_core_at_vertex ctx.toAmbientSectionNineContext
    ctx.criticalPath.a' ⟨actor, hactor⟩

/-- The opening paragraph of Section Ten, with Hypothesis Two retained on the
original ambient group and every local conclusion on its embedded graph group. -/
public theorem sectionTenOpeningData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    SectionTenOpeningData ctx.Γ ctx.criticalPath middle := by
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨horbit, hleft, hright, hne⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨hmodel, hcard⟩ := lemma_nine_three_ambient
    ctx.toAmbientSectionNineContext hb middle horbit
  obtain ⟨hfirst, hterminal⟩ := opening_noncontainments ctx middle hpath
  exact {
    quotient_model := hmodel
    center_card := hcard
    center_direct_product := nine_three_center_split ctx.toAmbientSectionNineContext
      hb horbit hleft hright hne
    center_omega := (nine_three_core_omega_eq_center
      ctx.toAmbientSectionNineContext hb middle horbit).symm
    first_noncontainment := hfirst
    terminal_noncontainment := hterminal
    endpoint_centralizer := opening_centralizer ctx }

/-- The original single-carrier context recovers the same opening package. -/
public theorem sectionTenOpeningData_legacy
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    SectionTenOpeningData ctx.Γ ctx.criticalPath middle := by
  exact sectionTenOpeningData ctx.toAmbientContext middle hpath


/-- The local endpoint centralizer assertion expressed in the original ambient
group, through the context's injective embedding. -/
public theorem sectionTenOpeningData_ambientCentralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B) :
    (GAt ctx.Γ ctx.criticalPath.a').map embedding ⊓
        Subgroup.centralizer ((VAt ctx.Γ ctx.criticalPath.a').map embedding : Set H) ≤
      (QAt ctx.Γ ctx.criticalPath.a').map embedding := by
  rintro element ⟨⟨preimage, _, rfl⟩, hcentral⟩
  apply Subgroup.mem_map_of_mem
  apply opening_centralizer ctx
  change embedding preimage ∈ Subgroup.centralizer
    ((VAt ctx.Γ ctx.criticalPath.a').map embedding : Set H) at hcentral
  rw [Subgroup.mem_centralizer_iff] at hcentral ⊢
  intro vector hvector
  apply ctx.embedding_injective
  simpa only [map_mul] using
    hcentral (embedding vector) (Subgroup.mem_map_of_mem embedding hvector)

end Stellmacher.SectionTen
