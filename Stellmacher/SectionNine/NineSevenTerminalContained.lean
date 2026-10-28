module

public import Stellmacher.SectionNine.NineSevenSourceAlternatives
public import Stellmacher.SectionNine.NineSevenSourceOddSetup
public import Stellmacher.SectionNine.NineSevenTerminalContainedCommutatorBound
public import Stellmacher.SectionNine.NineNextVModule
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer

/-!
# The actual neighborhood-contained branch of (9.7)

Use the larger source odd-W join, which is abelian and penultimate-contained.
When it is terminal-contained, the rank-two interval gives the source
commutator alternatives. Otherwise its abelianness excludes the terminal
center; the actual contained W then has commutator exactly the critical
line. The source normality-alternative theorem excludes both outcomes.

The public statement keeps the original uniform-neighborhood join and all
common (9.7) data unchanged. The proof rewrites that join as the initial W
and uses the explicitly constructed, larger two-step-walk join only as an
auxiliary subgroup. It does not equate the two joins or assume either source
normality conclusion. Source: Stellmacher (9.7), printed p.54 / PDF p.44,
the terminal-contained paragraph and the following noncontained paragraph.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem eq_plane_of_line_lt
    {G : Type u} [Group G] [Finite G] (line middle plane : Subgroup G)
    (hline : Nat.card line = 2) (hplane : Nat.card plane ≤ 4)
    (hlineMiddle : line ≤ middle) (hmidPlane : middle ≤ plane) (hne : middle ≠ line) :
    middle = plane := by
  have hlt : Nat.card line < Nat.card middle := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hlineMiddle)
    intro hcard
    exact hne (Subgroup.eq_of_le_of_card_ge hlineMiddle hcard.ge).symm
  have hdiv := Subgroup.card_dvd_of_le hlineMiddle
  rw [hline] at hlt hdiv
  obtain ⟨factor, hfactor⟩ := hdiv
  apply Subgroup.eq_of_le_of_card_ge hmidPlane
  omega

public theorem nine_seven_no_large_distance_of_neighbor_join_le_terminal
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
    (hterminal : sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤
      GAt ctx.Γ ctx.criticalPath.a') :
    False := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  let W := GeneratedNeighborhoodV Gamma cp.a
  let U := SourceInitialOddJoin Gamma cp.a
  let Aend := VAt Gamma cp.a'
  let R := ⁅Aend, ZAt Gamma cp.a⁆
  let Z := ZAt Gamma cp.a'
  let P := ZAt Gamma penultimate
  let D := R ⊔ Z
  have hlongLocal : 7 < ctx.toLocalContext.criticalPath.length := hlong
  have hfour := (hstartData cp.a ⟨1, Gamma.act_one _⟩).2
  have hgeometry := nine_seven_commutator_geometry ctx hb third hpath hindex
    hfirstCard hfirstModel hendCard hendModel hstartData (by omega)
  have hRcard : Nat.card R = 2 := hgeometry.1
  have hRP : R ≤ P := hgeometry.2.2.1
  obtain ⟨aligner, hpenAlign, hendAlign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Gamma cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Gamma cp.a penultimate := ⟨aligner, hpenAlign⟩
  have hendOrbit : IsConjugateVertex Gamma cp.firstStep cp.a' := ⟨aligner, hendAlign⟩
  have hPcard : Nat.card P = 4 := (hstartData penultimate hpenOrbit).2
  have hpenEnd : Gamma.adjacent penultimate cp.a' := by
    have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
    have hend : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length, by omega⟩ := Fin.ext (by dsimp [cp]; omega)
    rwa [hend, cp.path_end] at hadj
  have hZP : Z ≤ P := ((nine_seven_center_join ctx penultimate hpenOrbit).2 cp.a'
    ((mem_neighborhood_iff_adjacent Gamma).mpr hpenEnd)).2
  have hDP : D ≤ P := sup_le hRP hZP
  have hDcard : Nat.card D ≤ 4 := (Subgroup.card_le_of_le hDP).trans_eq hPcard
  have hsourceSetup := nine_seven_source_initial_odd_setup ctx hb third hpath hindex
    hfirstCard hfirstModel hendCard hendModel hstartData hlong
  have hUpen : U ≤ GAt Gamma penultimate := hsourceSetup.1
  have hUabelian : ⁅U, U⁆ = ⊥ := hsourceSetup.2
  have hWterminal : W ≤ GAt Gamma cp.a' := by
    rw [nine_seven_initial_neighbor_join_eq_neighborhood ctx] at hterminal
    exact hterminal
  have hWpen : W ≤ GAt Gamma penultimate := by
    rw [nine_seven_initial_neighbor_join_eq_neighborhood ctx] at hU
    exact hU
  have hWodd : W ≤ SourceOddW Gamma cp.firstStep := by
    unfold W GeneratedNeighborhoodV
    apply sSup_le
    rintro subgroup ⟨endpoint, hendpoint, rfl⟩
    exact le_sSup ⟨cp.a,
      (mem_neighborhood_iff_adjacent Gamma).mpr (Gamma.adjacent_symm cp.firstStep_adj),
      endpoint, hendpoint, rfl⟩
  have hoddU : SourceOddW Gamma cp.firstStep ≤ U :=
    le_sSup ⟨cp.firstStep, (mem_neighborhood_iff_adjacent Gamma).mpr cp.firstStep_adj, rfl⟩
  have hWU : W ≤ U := hWodd.trans hoddU
  have hfirstW : VAt Gamma cp.firstStep ≤ W :=
    nine_seven_neighbor_module_le_neighborhood Gamma cp.firstStep_adj
  have hRfirst : R ≤ VAt Gamma cp.firstStep :=
    (nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_left
  have hRW : R ≤ W := hRfirst.trans hfirstW
  have hZaW : ZAt Gamma cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Gamma cp).first_containment.1.trans hfirstW
  have hRcomm : R ≤ ⁅W, Aend⁆ := by
    rw [Subgroup.commutator_comm W]
    exact Subgroup.commutator_mono le_rfl hZaW
  have hWcomm : ⁅W, Aend⁆ ≤ D :=
    nine_seven_subgroup_terminal_commutator_le ctx hb hfour hendModel W hWpen hWterminal
  apply nine_seven_source_commutator_alternatives_impossible ctx (by omega)
    (hstartData cp.a ⟨1, Gamma.act_one _⟩).1 hfirstModel
  by_cases hSourceTerminal : U ≤ GAt Gamma cp.a'
  · have hUcomm : ⁅U, Aend⁆ ≤ D :=
      nine_seven_subgroup_terminal_commutator_le ctx hb hfour hendModel U hUpen hSourceTerminal
    by_cases hline : ⁅W, Aend⁆ = R
    · exact Or.inl hline
    · have hfull := eq_plane_of_line_lt R ⁅W, Aend⁆ D hRcard hDcard hRcomm hWcomm hline
      exact Or.inr (le_antisymm (hUcomm.trans_eq hfull.symm)
        (Subgroup.commutator_mono hWU le_rfl))
  · have hZcard : Nat.card Z = 2 :=
      (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour cp.a' hendOrbit).1
    have hnotRZ : ¬ R ≤ Z := by
      obtain ⟨_, hbaseComm⟩ := nine_next_center_and_commutator_of_initial_four
        ctx.toLocalContext hfour cp.a' hendOrbit
      have hkernel := (nine_next_v_module_kernel_of_center_and_commutator ctx hb
        cp.a' hendOrbit hZcard hbaseComm).2.2
      intro hRZ
      apply cp.critical.2
      intro actor hactor
      apply (hkernel actor ((lemma_seven_four ctx.sectionSeven Gamma cp).first_containment.1.trans
        (lemma_seven_four ctx.sectionSeven Gamma cp).first_containment.2 hactor)).mp
      exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hRZ
    have hnotZR : ¬ Z ≤ R := by
      intro hZR
      exact hnotRZ (Subgroup.eq_of_le_of_card_ge hZR (by omega)).ge
    obtain ⟨point, hpoint, houtside⟩ := SetLike.not_le_iff_exists.mp hnotZR
    have hPD : P ≤ D := nine_five_index_two_span_of_element R P D hRP
      (by change Nat.card P = 2 * Nat.card R; omega) le_sup_left point (hZP hpoint) houtside
        (Subgroup.mem_sup_right hpoint)
    have hnotZU : ¬ Z ≤ U := by
      intro hZU
      have hPU : P ≤ U := hPD.trans (sup_le (hRW.trans hWU) hZU)
      have hUC : U ≤ Subgroup.centralizer (P : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUabelian).trans
          (Subgroup.centralizer_le hPU)
      have hUQ : U ≤ QAt Gamma cp.a := by
        unfold U SourceInitialOddJoin
        apply sSup_le
        rintro subgroup ⟨neighbor, hneighbor, rfl⟩
        have hdist : Gamma.distance neighbor cp.a ≤ 1 := Gamma.distance_le_of_path 1
          ![neighbor, cp.a] (by
            intro step
            fin_cases step
            exact Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).mp hneighbor))
        exact source_odd_w_le_core_of_distance Gamma cp neighbor cp.a (by dsimp [cp] at *; omega)
      have htwo : IsPGroup 2 U := nine_seven_subgroup_isTwoGroup_of_le_vertex_core
        Gamma cp.a U hUQ
      have hcore := nine_three_orbit_pgroup_centralizer ctx.toLocalContext penultimate
        hpenOrbit U htwo hUpen hUC
      apply hSourceTerminal
      exact hcore.trans (((lemma_seven_three ctx.sectionSeven Gamma).sylow_and_core
        penultimate cp.a' ((mem_neighborhood_iff_adjacent Gamma).mpr hpenEnd) default).2.2)
    have hAN : Aend ≤ Subgroup.normalizer (SourceOddW Gamma cp.firstStep : Set G) := by
      apply (lemma_seven_four ctx.sectionSeven Gamma cp).reverse_containment.2.trans
      apply Subgroup.le_normalizer_iff.mpr
      intro actor hactor element helement
      have hfix : Gamma.act actor⁻¹ cp.firstStep = cp.firstStep :=
        (Set.ext_iff.mp (Gamma.stabilizer_def cp.firstStep) actor⁻¹).mp
          ((GAt Gamma cp.firstStep).inv_mem hactor)
      have hact := sourceOddW_act Gamma actor⁻¹ cp.firstStep
      simp only [inv_inv, hfix] at hact
      exact hact.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom helement
    have hcommU : ⁅W, Aend⁆ ≤ U :=
      ((Subgroup.commutator_mono hWodd le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hAN)).trans hoddU
    apply Or.inl
    by_contra hline
    have hfull := eq_plane_of_line_lt R ⁅W, Aend⁆ D hRcard hDcard hRcomm hWcomm hline
    exact hnotZU ((le_sup_right.trans hfull.ge).trans hcommU)

end Stellmacher.SectionNine

