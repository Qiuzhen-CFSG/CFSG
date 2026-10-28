module
public import Stellmacher.SectionNine.NineSevenTerminalContainedHelpers
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction

/-!
# The terminal-contained neighbor-join commutator bound

For any subgroup lying in both the penultimate and terminal stabilizers,
its commutator with the terminal module lies in R joined with the terminal
center, where R is the actual critical commutator with the initial center.
The original long-distance initial-neighbor-join interface is retained as
a wrapper. The general theorem also applies to the larger source odd-W join.

The terminal core has index two in the terminal edge stabilizer. The initial
center lies in this edge and escapes that core by criticality, so the core
and initial center generate the edge. The core acts on the terminal module
with commutator equal to its center. This shows that both edge generators
normalize the required commutator bound, and the join commutator lemma
finishes. This theorem supplies the algebraic bound for the terminal-contained
normality case; it does not assert that case's final contradiction.

Source: Stellmacher (9.7), printed p.54 / PDF p.44, the paragraph beginning
with containment of U in the terminal stabilizer.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

private theorem normalizes_join_of_commutator_bound
    {G : Type u} [Group G] (actors source layer : Subgroup G)
    (hnormal : actors ≤ Subgroup.normalizer (layer : Set G))
    (hcomm : ⁅actors, source⁆ ≤ layer) :
    actors ≤ Subgroup.normalizer ((source ⊔ layer : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor vector hvector
  have hmap : (source ⊔ layer).map (MulAut.conj actor).toMonoidHom ≤ source ⊔ layer := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨element, helement, rfl⟩
      have hcommMem := hcomm (Subgroup.commutator_mem_commutator hactor helement)
      have hmul := (source ⊔ layer).mul_mem
        (Subgroup.mem_sup_right hcommMem) (Subgroup.mem_sup_left helement)
      change actor * element * actor⁻¹ ∈ source ⊔ layer
      simpa only [MulAut.conj_apply, commutatorElement_def, mul_assoc,
        inv_mul_cancel, mul_one] using hmul
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormal hactor)).le.trans le_sup_right
  exact hmap ⟨vector, hvector, rfl⟩

public theorem nine_seven_subgroup_terminal_commutator_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (subgroup : Subgroup G)
    (hpen : subgroup ≤ GAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩))
    (hterminal : subgroup ≤ GAt ctx.Γ ctx.criticalPath.a') :
    ⁅subgroup, VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  let Q := QAt Γ cp.a'
  let V := VAt Γ cp.a'
  let initial := ZAt Γ cp.a
  let Z := ZAt Γ cp.a'
  let R := ⁅V, initial⁆
  let edge := GAt Γ cp.a' ⊓ GAt Γ penultimate
  have hpenTerminal : Γ.adjacent penultimate cp.a' := by
    have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
    have hend : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length, by omega⟩ := Fin.ext (by dsimp [cp]; omega)
    rwa [hend, cp.path_end] at hadj
  have hQG : Q ≤ GAt Γ cp.a' := by
    change Γ.twoCoreAt cp.a' ≤ Γ.stabilizer cp.a'
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQedge : Q ≤ edge := le_inf hQG
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a' penultimate
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hpenTerminal)) default).2.2)
  have hZfirst : initial ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hInitialG : initial ≤ GAt Γ cp.a' := hZfirst.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hInitialPen : initial ≤ GAt Γ penultimate := by
    apply (hZfirst.trans (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1).trans
    change Γ.twoCoreAt penultimate ≤ Γ.stabilizer penultimate
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hInitialEdge : initial ≤ edge := le_inf hInitialG hInitialPen
  have hEdgeIndex : QuotientCardEq edge Q 2 :=
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a' hendModel).edge_card
      penultimate (Γ.adjacent_symm hpenTerminal)
  obtain ⟨vector, hvector, houtside⟩ := SetLike.not_le_iff_exists.mp cp.critical.2
  have hedgeJoin : edge ≤ Q ⊔ initial := nine_five_index_two_span_of_element Q edge
    (Q ⊔ initial) hQedge hEdgeIndex le_sup_left vector (hInitialEdge hvector) houtside
      (Subgroup.mem_sup_right hvector)
  have hUjoin : subgroup ≤ Q ⊔ initial := (le_inf hterminal hpen).trans hedgeJoin
  obtain ⟨endpointActor, _, hendpoint⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hVQ : ⁅V, Q⁆ = Z := (nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour cp.a' ⟨endpointActor, hendpoint⟩).2
  have hQV : ⁅Q, V⁆ ≤ Z := by rw [Subgroup.commutator_comm, hVQ]
  have hRV : R ≤ V := (nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_right
  have hQnormalizes : Q ≤ Subgroup.normalizer ((R ⊔ Z : Subgroup G) : Set G) :=
    normalizes_join_of_commutator_bound Q R Z
      (hQG.trans (stabilizer_le_normalizer_z Γ cp.a'))
      ((Subgroup.commutator_mono le_rfl hRV).trans hQV)
  have hInitialNormalizes : initial ≤ Subgroup.normalizer ((R ⊔ Z : Subgroup G) : Set G) :=
    (le_inf (Subgroup.normalizer_commutator_ge_right V initial)
      (hInitialG.trans (stabilizer_le_normalizer_z Γ cp.a'))).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup R Z)
  apply (Subgroup.commutator_mono hUjoin le_rfl).trans
  exact nine_five_commutator_join_le Q initial V (R ⊔ Z) hQnormalizes hInitialNormalizes
    (hQV.trans le_sup_right) ((Subgroup.commutator_comm initial V).le.trans le_sup_left)

public theorem nine_seven_initial_join_terminal_commutator_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (_hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (_hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (_hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (_hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (_hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
    (hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hlong : 7 < ctx.criticalPath.length)
    (hU : sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤
      GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩))
    (hterminal : sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤
      GAt ctx.Γ ctx.criticalPath.a') :
    ⁅sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor}, VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a' := by
  exact nine_seven_subgroup_terminal_commutator_le ctx hb
    (hstartData ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2 hendModel _ hU hterminal

end Stellmacher.SectionNine
