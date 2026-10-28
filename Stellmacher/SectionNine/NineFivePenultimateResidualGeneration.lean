module

public import Stellmacher.SectionNine.NineFivePenultimateJoinAction
public import Stellmacher.SectionNine.CubicLocalAction
public import Stellmacher.SectionFiveToSeven.ResidualTransport
public import Stellmacher.SectionNine.NineTwoCoreQuotientFromFour

/-!
# The penultimate residual and two distinct neighbor cores

In a cubic neighborhood, a neighbor core outside the central vertex core
acts transitively on the other two neighbors. Thus two distinct neighbor
cores contain every neighbor core, and contain the conjugate closure of
either one under the central stabilizer. This is the missing generation
passage in the first line of Stellmacher (9.5), printed p.53 / PDF p.43.

The genuine (7.6)(b) noncontainment and conjugate-closure bound transport
along an aligned edge to the penultimate vertex. Critical-path minimality
ensures that the predecessor and terminal really are distinct neighbors.
The cubic quotient follows from initial center order four using the proved
quotient producer. The unconditional center-order input remains the separate
ambient (9.3) task; this module does not claim the unconditional (9.5) target.

Source: `refs/files/stellmacher-n-group.pdf`, printed pp.52–53 / PDF pp.42–43.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem residualJoin_core_le_self
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (graph : CosetGraphContext G T A B) (vertex : graph.Vertex) :
    QAt graph vertex ≤ GAt graph vertex := by
  rw [QAt, q, graph.twoCoreAt_def]
  exact twoCoreIn_le _

private theorem residualJoin_core_le_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (hyp : SectionSevenHypotheses G T A B)
    (graph : CosetGraphContext G T A B) {first second : graph.Vertex}
    (hadj : graph.adjacent first second) : QAt graph first ≤ GAt graph second :=
  ((lemma_seven_three hyp graph).sylow_and_core first second
    ((mem_neighborhood_iff_adjacent graph).mpr hadj) default).2.2

public theorem nine_five_cubic_neighbor_core_le_join
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (hyp : SectionSevenHypotheses G T A B)
    (graph : CosetGraphContext G T A B) {middle previous terminal : graph.Vertex}
    (hmodel : QuotientIsModel (GAt graph middle) (QAt graph middle) SL2Two)
    (hprevious : graph.adjacent middle previous)
    (hterminal : graph.adjacent middle terminal) (hne : previous ≠ terminal)
    (hout : ¬ QAt graph previous ≤ QAt graph middle)
    (neighbor : graph.Vertex) (hadj : graph.adjacent middle neighbor) :
    QAt graph neighbor ≤ QAt graph previous ⊔ QAt graph terminal := by
  by_cases heq : neighbor = previous
  · rw [heq]
    exact le_sup_left
  have htrans := (cubic_local_action_of_sl2Two_quotient graph hyp middle hmodel).punctured_transitivity
    previous hprevious (QAt graph previous)
      (le_inf (residualJoin_core_le_neighbor hyp graph (graph.adjacent_symm hprevious))
        (residualJoin_core_le_self graph previous)) hout
  obtain ⟨actor, hactor⟩ := htrans (d := terminal) (l := neighbor)
    ⟨(mem_neighborhood_iff_adjacent graph).mpr hterminal, by simpa using Ne.symm hne⟩
    ⟨(mem_neighborhood_iff_adjacent graph).mpr hadj, by simpa using heq⟩
  rw [← hactor, QAt, q_act]
  rintro element ⟨generator, hgenerator, rfl⟩
  change (actor : G)⁻¹ * generator * (actor : G)⁻¹⁻¹ ∈ _
  rw [inv_inv]
  exact (QAt graph previous ⊔ QAt graph terminal).mul_mem
    ((QAt graph previous ⊔ QAt graph terminal).mul_mem
      (Subgroup.mem_sup_left ((QAt graph previous).inv_mem actor.property))
      (Subgroup.mem_sup_right hgenerator)) (Subgroup.mem_sup_left actor.property)

public theorem nine_five_cubic_neighbor_closure_le_join
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (hyp : SectionSevenHypotheses G T A B)
    (graph : CosetGraphContext G T A B) {middle previous terminal : graph.Vertex}
    (hmodel : QuotientIsModel (GAt graph middle) (QAt graph middle) SL2Two)
    (hprevious : graph.adjacent middle previous)
    (hterminal : graph.adjacent middle terminal) (hne : previous ≠ terminal)
    (hout : ¬ QAt graph previous ≤ QAt graph middle) :
    conjugateClosure (QAt graph terminal) (GAt graph middle) ≤
      QAt graph previous ⊔ QAt graph terminal := by
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  have hfix : graph.act (actor : G)⁻¹ middle = middle :=
    (Set.ext_iff.mp (graph.stabilizer_def middle) _).mp
      ((GAt graph middle).inv_mem actor.property)
  have hadj := adjacent_act graph (actor : G)⁻¹ hterminal
  rw [hfix] at hadj
  apply nine_five_cubic_neighbor_core_le_join hyp graph hmodel hprevious hterminal hne
    hout _ hadj
  rw [QAt, q_act, inv_inv]
  exact Subgroup.mem_map.mpr ⟨generator, generator.property, rfl⟩

private theorem residualJoin_edge_alignment
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) neighbor) :
    ∃ actor : G, ctx.Γ.act actor ctx.criticalPath.a =
      ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∧
      ctx.Γ.act actor ctx.criticalPath.firstStep = neighbor := by
  obtain ⟨mover, hmiddle, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨wheel, hwheel⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    _ ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (nine_five_penultimate_adjacent ctx))
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  refine ⟨mover * (wheel : G), ?_, ?_⟩
  · rw [ctx.Γ.act_mul, hmiddle]
    exact (Set.ext_iff.mp (ctx.Γ.stabilizer_def _) _).mp wheel.property
  · rw [ctx.Γ.act_mul, hterminal, hwheel]

public theorem nine_five_penultimate_neighbor_core_not_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) neighbor) :
    ¬ QAt ctx.Γ neighbor ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  obtain ⟨actor, hmiddle, hneighbor⟩ := residualJoin_edge_alignment ctx neighbor hadj
  intro hle
  rw [← hmiddle, ← hneighbor, QAt, QAt, q_act, q_act] at hle
  have hinitial := (Subgroup.map_le_map_iff_of_injective
    (MulAut.conj actor⁻¹).injective).mp hle
  apply (lemma_seven_six ctx.sectionSeven ctx.Γ ctx.criticalPath).next_residual_core.1
  refine le_trans ?_ hinitial
  rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
    residual_core_eq_inter_core]
  exact inf_le_right

public theorem nine_five_previous_ne_terminal
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) (previous : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) previous) : previous ≠ ctx.criticalPath.a' := by
  obtain ⟨index, hindex, rfl⟩ := hpath
  intro heq
  have hbound := path_distance_le ctx.Γ ctx.criticalPath 0
    (ctx.criticalPath.length - 2) (by omega) (Nat.sub_le _ _)
  have hpoint : ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 2, by omega⟩ = ctx.criticalPath.a' := by
    convert heq using 1
    exact congrArg ctx.criticalPath.path (Fin.ext hindex.symm)
  rw [hpoint, show ctx.criticalPath.path ⟨0, by omega⟩ = ctx.criticalPath.a from
    ctx.criticalPath.path_start, ctx.criticalPath.endpoint_distance] at hbound
  omega

private theorem residualJoin_residual_act
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (graph : CosetGraphContext G T A B) (actor : G) (vertex : graph.Vertex) :
    EAt graph (graph.act actor vertex) =
      (EAt graph vertex).map (MulAut.conj actor⁻¹).toMonoidHom := by
  change graph.twoResidualAt (graph.act actor vertex) =
    (graph.twoResidualAt vertex).map (MulAut.conj actor⁻¹).toMonoidHom
  rw [graph.twoResidualAt_def, graph.twoResidualAt_def]
  change twoResidualIn (stabilizer graph (graph.act actor vertex)) = _
  rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
  rfl

private theorem residualJoin_map_closure_le
    {G : Type u} [Group G] (equiv : G ≃* G) (seed actors : Subgroup G) :
    (conjugateClosure seed actors).map equiv.toMonoidHom ≤
      conjugateClosure (seed.map equiv.toMonoidHom) (actors.map equiv.toMonoidHom) := by
  rw [conjugateClosure, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro element ⟨preimage, ⟨actor, generator, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨⟨equiv actor, Subgroup.mem_map_of_mem equiv.toMonoidHom actor.property⟩,
    ⟨equiv generator, Subgroup.mem_map_of_mem equiv.toMonoidHom generator.property⟩, ?_⟩
  simp only [map_mul, map_inv]
  rfl

private theorem residualJoin_closure_mono
    {G : Type u} [Group G] {seed bigger : Subgroup G} (actors : Subgroup G)
    (hle : seed ≤ bigger) : conjugateClosure seed actors ≤ conjugateClosure bigger actors := by
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  exact Subgroup.subset_closure ⟨actor, ⟨generator, hle generator.property⟩, rfl⟩

public theorem nine_five_penultimate_residual_le_neighbor_closure
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) neighbor) :
    EAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
        conjugateClosure (QAt ctx.Γ neighbor) (GAt ctx.Γ
          (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) := by
  obtain ⟨actor, hmiddle, hneighbor⟩ := residualJoin_edge_alignment ctx neighbor hadj
  have hcore : twoCoreIn (e ctx.Γ ctx.criticalPath.firstStep) ≤
      q ctx.Γ ctx.criticalPath.firstStep := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hbound := (lemma_seven_six ctx.sectionSeven ctx.Γ ctx.criticalPath).next_residual_core.2
  have hinitial := hbound.trans (residualJoin_closure_mono _ hcore)
  have hmapped := (Subgroup.map_mono (f := (MulAut.conj actor⁻¹).toMonoidHom)
    hinitial).trans (residualJoin_map_closure_le (MulAut.conj actor⁻¹) _ _)
  rw [← hmiddle, ← hneighbor, residualJoin_residual_act, GAt, stabilizer_act,
    QAt, q_act]
  exact hmapped

private theorem residualJoin_quotient_model_act
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (graph : CosetGraphContext G T A B) (actor : G) (vertex : graph.Vertex)
    (hmodel : QuotientIsModel (GAt graph vertex) (QAt graph vertex) SL2Two) :
    QuotientIsModel (GAt graph (graph.act actor vertex))
      (QAt graph (graph.act actor vertex)) SL2Two := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  change QuotientIsModel (stabilizer graph (graph.act actor vertex))
    (q graph (graph.act actor vertex)) SL2Two
  rw [stabilizer_act, q_act]
  let equiv := (GAt graph vertex).equivMapOfInjective
    (MulAut.conj actor⁻¹).toMonoidHom (MulAut.conj actor⁻¹).injective
  refine ⟨projection.comp equiv.symm.toMonoidHom,
    hsurj.comp equiv.symm.surjective, ?_⟩
  ext point
  change projection (equiv.symm point) = 1 ↔
    (point : G) ∈ (QAt graph vertex).map (MulAut.conj actor⁻¹).toMonoidHom
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_map_equiv]
  have heq : (equiv.symm point : G) = (MulAut.conj actor⁻¹).symm (point : G) := by
    apply (MulAut.conj actor⁻¹).injective
    change (equiv (equiv.symm point) : G) = _
    simp only [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (equiv.apply_symm_apply point)
  change (equiv.symm point : G) ∈ QAt graph vertex ↔ _
  rw [heq]

public theorem nine_five_penultimate_residual_le_join_of_initial_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev) :
    EAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
        QAt ctx.Γ prev ⊔ QAt ctx.Γ ctx.criticalPath.a' := by
  have hterminal := nine_five_penultimate_adjacent ctx.toLocalContext
  have hprevious := ctx.Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb prev hpath)
  have hout := nine_five_penultimate_neighbor_core_not_le ctx.toLocalContext prev hprevious
  have hne := nine_five_previous_ne_terminal ctx.toLocalContext hb prev hpath
  obtain ⟨actor, hmiddle, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hmodel := residualJoin_quotient_model_act ctx.Γ actor ctx.criticalPath.a
    (nine_two_core_quotient_of_card_four ctx hfour)
  rw [hmiddle] at hmodel
  exact (nine_five_penultimate_residual_le_neighbor_closure ctx.toLocalContext
    ctx.criticalPath.a' hterminal).trans
      (nine_five_cubic_neighbor_closure_le_join ctx.sectionSeven ctx.Γ hmodel
        hprevious hterminal hne hout)

end Stellmacher.SectionNine

