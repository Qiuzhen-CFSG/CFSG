module
public import Stellmacher.SectionNine.NineSevenTerminalContainedHelpers
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer

/-!
# The penultimate-center commutator in the noncontained case

In the long-distance branch of (9.7), suppose the actual initial neighbor
join U lies in the penultimate stabilizer and does not lie in the terminal
stabilizer. Then [U,Z_penultimate] is exactly the critical commutator R.

The abelian group U contains R and hence fixes it pointwise. The order-two
line R has index two in the penultimate center, so invariance gives the
commutator bound into R. If the commutator vanished, the initial-orbit
two-subgroup centralizer theorem would put U in the penultimate core, which
lies in the terminal stabilizer. Thus the commutator is nontrivial, and the
order of R gives equality.

This is the first center relation for the noncontained terminal normality
case. Source: Stellmacher (9.7), printed p.54 / PDF p.44, the paragraphs
beginning with noncontainment of U in the terminal stabilizer.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_seven_noncontained_penultimate_center_commutator
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
    ⁅sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor},
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)⁆ =
      ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlocalLength : 7 < ctx.toLocalContext.criticalPath.length := hlong
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  let U := sSup {subgroup : Subgroup G | ∃ neighbor,
    neighbor ∈ Neighborhood Γ cp.a ∧ subgroup = GeneratedNeighborhoodV Γ neighbor}
  let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
  let Z := ZAt Γ penultimate
  have hgeometry := nine_seven_commutator_geometry ctx hb third hpath hindex hfirstCard
    hfirstModel hendCard hendModel hstartData (by omega)
  have hRcard : Nat.card R = 2 := hgeometry.1
  have hRZ : R ≤ Z := hgeometry.2.2.1
  obtain ⟨endpointActor, hpen, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨endpointActor, hpen⟩
  have hZcard : Nat.card Z = 4 := (hstartData penultimate hpenOrbit).2
  have hfirstMember : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hfirstU : VAt Γ cp.firstStep ≤ U := by
    rw [← nine_seven_neighbor_neighborhood_eq_module ctx cp.firstStep hfirstMember]
    exact le_sSup ⟨cp.firstStep, hfirstMember, rfl⟩
  have hRU : R ≤ U := ((nine_seven_terminal_initial_commutator_le_modules ctx).trans
    inf_le_left).trans hfirstU
  have habelian : ⁅U, U⁆ = ⊥ := nine_seven_initial_neighbor_join_abelian ctx.toLocalContext
    (by omega)
  have hUC : U ≤ Subgroup.centralizer (R : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp habelian).trans
      (Subgroup.centralizer_le hRU)
  have hRindex : (R.subgroupOf Z).index = 2 := by
    have hprod := (R.subgroupOf Z).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRZ).toEquiv, hRcard, hZcard] at hprod
    omega
  have hcomm : ⁅U, Z⁆ ≤ R := by
    rw [Subgroup.commutator_comm]
    exact nine_seven_normalized_index_two_commutator_le Z R U hRindex
      (hU.trans (stabilizer_le_normalizer_z Γ penultimate))
      (hUC.trans (Subgroup.centralizer_le_normalizer _))
  have hne : ⁅U, Z⁆ ≠ ⊥ := by
    intro hbot
    have htwo : IsPGroup 2 U := nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ cp.a U
      (nine_seven_neighbor_join_le_own_core ctx.toLocalContext (by omega) cp.a)
    have hcore : U ≤ QAt Γ penultimate := nine_three_orbit_pgroup_centralizer
      ctx.toLocalContext penultimate hpenOrbit U htwo hU
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    apply hterminal
    apply hcore.trans
    have hpenTerminal : Γ.adjacent penultimate cp.a' := by
      have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
      have hend : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
          ⟨cp.length, by omega⟩ := Fin.ext (by dsimp [cp]; omega)
      rwa [hend, cp.path_end] at hadj
    exact ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hpenTerminal) default).2.2
  apply Subgroup.eq_of_le_of_card_ge hcomm
  rw [hRcard]
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne

end Stellmacher.SectionNine
