module
public import Stellmacher.SectionNine.NineSevenNoncontainedCenterCommutator
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra

/-!
# The first-center identity in the noncontained case

For the actual initial neighbor join U, its containment in the penultimate
stabilizer and noncontainment in the terminal stabilizer identify the critical
commutator R with the first-step center.

The initial core acts on each neighboring order-eight module with commutator
inside the initial center. Supremum induction propagates this to the actual
neighborhood join. The penultimate center lies in the initial core by critical
minimality; the preceding commutator theorem therefore puts R in the initial
center. Its intersection with the terminal core is the first-center line:
the line centralizes the terminal module, and any further element would
generate the initial center and contradict criticality. Cardinality finishes
the identification.

This supplies the center equality for the noncontained terminal normality
case, using the repository's unchanged neighborhood definition. Source:
Stellmacher (9.7), printed p.54 / PDF p.44.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

private theorem initial_neighborhood_core_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 2 < ctx.criticalPath.length)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, QAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  let Q := QAt Γ cp.a
  let Z := ZAt Γ cp.a
  let family : Set (Subgroup G) := {subgroup | ∃ neighbor,
    neighbor ∈ Neighborhood Γ cp.a ∧ subgroup = VAt Γ neighbor}
  have hWQ : W ≤ Q := nine_seven_neighborhood_le_own_core ctx.toLocalContext hb cp.a
  have hQG : Q ≤ GAt Γ cp.a := by
    change Γ.twoCoreAt cp.a ≤ Γ.stabilizer cp.a
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hWN : W ≤ Subgroup.normalizer (Z : Set G) :=
    hWQ.trans (hQG.trans (stabilizer_le_normalizer_z Γ cp.a))
  apply Subgroup.commutator_le.mpr
  intro point hpoint actor hactor
  have hgood : point ∈ Subgroup.normalizer (Z : Set G) ∧
      ∀ mover ∈ Q, ⁅point, mover⁆ ∈ Z := by
    change point ∈ sSup family at hpoint
    rw [sSup_eq_iSup'] at hpoint
    refine Subgroup.iSup_induction (fun subgroup : family => (subgroup : Subgroup G))
      (C := fun point => point ∈ Subgroup.normalizer (Z : Set G) ∧
        ∀ mover ∈ Q, ⁅point, mover⁆ ∈ Z) hpoint ?_ ?_ ?_
    · intro subgroup element helement
      have hmember : element ∈ W := (le_sSup subgroup.property) helement
      refine ⟨hWN hmember, ?_⟩
      obtain ⟨neighbor, hneighbor, heq⟩ := subgroup.property
      rw [heq] at helement
      obtain ⟨mover, hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hneighbor
      have hcard : Nat.card (VAt Γ neighbor) = 8 := by
        rw [← hmover, VAt, v_act, Subgroup.card_map_of_injective (MulAut.conj (mover : G)⁻¹).injective]
        exact hfirstCard
      exact Subgroup.commutator_le.mp
        (nine_seven_neighbor_core_module_commutator_le_center ctx.toLocalContext
          ((mem_neighborhood_iff_adjacent Γ).mp hneighbor) hcard hfour) element helement
    · exact ⟨(Subgroup.normalizer (Z : Set G)).one_mem, by simp⟩
    · rintro left right ⟨hleft, hleftComm⟩ ⟨hright, hrightComm⟩
      refine ⟨(Subgroup.normalizer (Z : Set G)).mul_mem hleft hright, ?_⟩
      intro mover hmover
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem
        ((Subgroup.mem_normalizer_iff.mp hleft _).mp (hrightComm mover hmover))
        (hleftComm mover hmover)
  exact hgood.2 actor hactor

public theorem nine_seven_initial_center_terminal_core_le_first_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a' ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let initial := ZAt Γ cp.a
  let line := ZAt Γ cp.firstStep
  let terminal := QAt Γ cp.a'
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have hline : line ≤ initial := by
    change z Γ cp.firstStep ≤ z Γ cp.a
    rw [hnext.1]
    obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
    rw [z, Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hlineCard : Nat.card line = 2 := nine_next_center_order_of_initial_four
    ctx.toLocalContext hfour
  have hlineCentral : line ≤ Subgroup.centralizer (VAt Γ cp.a' : Set G) := by
    change z Γ cp.firstStep ≤ _
    rw [hnext.2]
    exact (omegaOneCenter_le_centerAmbient _).trans ((centerAmbient_le_centralizer _).trans
      (Subgroup.centralizer_le (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2))
  obtain ⟨endpointActor, _, hendpoint⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hlineTerminal : line ≤ terminal := hlineCentral.trans
    (nine_three_module_centralizer_core_at_vertex ctx cp.a' ⟨endpointActor, hendpoint⟩)
  have hInitialCard : Nat.card initial = 4 := hfour
  have hindex : QuotientCardEq initial line 2 := by change Nat.card initial = 2 * Nat.card line; omega
  intro point hpoint
  by_contra houtside
  exact cp.critical.2 (nine_five_index_two_span_of_element line initial terminal hline hindex
    hlineTerminal point hpoint.1 houtside hpoint.2)

public theorem nine_seven_noncontained_commutator_eq_first_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
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
    (hterminal : ¬ sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤
      GAt ctx.Γ ctx.criticalPath.a') :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 7 < cp.length := hlong
  let penultimate := cp.path ⟨cp.length - 1, by omega⟩
  let U := sSup {subgroup : Subgroup G | ∃ neighbor,
    neighbor ∈ Neighborhood Γ cp.a ∧ subgroup = GeneratedNeighborhoodV Γ neighbor}
  let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
  have hfour := (hstartData cp.a ⟨1, Γ.act_one _⟩).2
  have hUQ : ⁅U, QAt Γ cp.a⁆ ≤ ZAt Γ cp.a := by
    rw [show U = GeneratedNeighborhoodV Γ cp.a from
      nine_seven_initial_neighbor_join_eq_neighborhood ctx]
    exact initial_neighborhood_core_commutator ctx (by omega) hfirstCard hfour
  have hcenterCore : ZAt Γ penultimate ≤ QAt Γ cp.a := by
    have hdist := path_distance_le Γ cp 0 (cp.length - 1) (by omega) (by omega)
    have hzero : (⟨0, by omega⟩ : Fin (cp.length + 1)) = 0 := Fin.ext rfl
    rw [hzero, cp.path_start, Nat.sub_zero] at hdist
    change Γ.distance cp.a penultimate ≤ cp.length - 1 at hdist
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    omega
  have hcomm : ⁅U, ZAt Γ penultimate⁆ = R :=
    nine_seven_noncontained_penultimate_center_commutator ctx hb third hpath hindex
      hfirstCard hfirstModel hendCard hendModel hstartData hlong hU hterminal
  have hRinitial : R ≤ ZAt Γ cp.a := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_rfl hcenterCore).trans hUQ
  have hRterminal : R ≤ QAt Γ cp.a' :=
    ((nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_right).trans
      (nine_seven_module_le_own_core ctx.toLocalContext hb cp.a')
  have hRline : R ≤ ZAt Γ cp.firstStep := (le_inf hRinitial hRterminal).trans
    (nine_seven_initial_center_terminal_core_le_first_center ctx hfour)
  apply Subgroup.eq_of_le_of_card_ge hRline
  have hlineCard : Nat.card (ZAt Γ cp.firstStep) = 2 :=
    nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  rw [nine_seven_terminal_initial_commutator_card_two ctx hb hfour hendCard, hlineCard]

end Stellmacher.SectionNine
