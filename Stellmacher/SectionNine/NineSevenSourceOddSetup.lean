module
public import Stellmacher.SectionNine.NineSevenSourceOddW
public import Stellmacher.SectionNine.NineSevenLongWitnessLocalization
public import Stellmacher.SectionNine.NineSevenNearbyNeighborhoodContraction

/-!
# The source odd-W initial join in the long-distance branch of (9.7)

With the actual order-eight modules, SL₂(2) local quotients, critical index-two
intersection, and critical distance greater than seven, the source-specific
initial join U is abelian and lies in the penultimate stabilizer. Here U is
`SourceInitialOddJoin`, built from the two-step `SourceOddW` groups. No equality
with the uniform one-step neighborhood join is used.

Expanding U into vertex centers gives four-edge generators. An eight-edge
walk joins any two generators, so odd critical distance greater than seven
forces commutation. For containment, the critical commutator has a center
witness at the first or third path vertex. Residual conjugates of each W
are compared modulo the centralizer two-core, which lies in the penultimate
stabilizer. Rooted two-arc transport moves nonexceptional W groups within
three-edge critical range of the penultimate vertex. In the exceptional
first-vertex case, expand W into the uniform neighborhood joins around that
vertex; residual neighbor transitivity moves each piece to the second path
vertex, where minimality supplies the required core containment.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.7), printed p.54 /
PDF p.44, the paragraph beginning with critical distance greater than seven;
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem source_initial_odd_join_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (initial : Γ.Vertex) (target : Subgroup G)
    (hcenters : ∀ first, first ∈ Neighborhood Γ initial →
      ∀ second, second ∈ Neighborhood Γ first →
      ∀ third, third ∈ Neighborhood Γ second →
      ∀ fourth, fourth ∈ Neighborhood Γ third →
      ZAt Γ fourth ≤ target) :
    SourceInitialOddJoin Γ initial ≤ target := by
  unfold SourceInitialOddJoin
  apply sSup_le
  rintro subgroup ⟨first, hfirst, rfl⟩
  unfold SourceOddW
  apply sSup_le
  rintro subgroup ⟨second, hsecond, third, hthird, rfl⟩
  change v Γ third ≤ target
  rw [v, Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨fourth, hfourth, rfl⟩
  exact hcenters first hfirst second hsecond third hthird fourth hfourth

private theorem source_initial_odd_join_abelian
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (hb : 8 < ctx.criticalPath.length) :
    ⁅SourceInitialOddJoin ctx.Γ ctx.criticalPath.a,
      SourceInitialOddJoin ctx.Γ ctx.criticalPath.a⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  apply source_initial_odd_join_le
  intro l₁ hl₁ l₂ hl₂ l₃ hl₃ l₄ hl₄
  apply Subgroup.le_centralizer_iff.mpr
  apply source_initial_odd_join_le
  intro r₁ hr₁ r₂ hr₂ r₃ hr₃ r₄ hr₄
  have hl₁' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hl₁
  have hl₂' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hl₂
  have hl₃' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hl₃
  have hl₄' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hl₄
  have hr₁' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hr₁
  have hr₂' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hr₂
  have hr₃' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hr₃
  have hr₄' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hr₄
  let vertices : Fin 9 → ctx.Γ.Vertex :=
    ![r₄, r₃, r₂, r₁, ctx.criticalPath.a, l₁, l₂, l₃, l₄]
  have hwalk : ∀ step : Fin 8,
      ctx.Γ.adjacent (vertices step.castSucc) (vertices step.succ) := by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hr₄'
    · exact ctx.Γ.adjacent_symm hr₃'
    · exact ctx.Γ.adjacent_symm hr₂'
    · exact ctx.Γ.adjacent_symm hr₁'
    · exact hl₁'
    · exact hl₂'
    · exact hl₃'
    · exact hl₄'
  have hdist := ctx.Γ.distance_le_of_path 8 vertices hwalk
  change ctx.Γ.distance r₄ l₄ ≤ 8 at hdist
  have hcore := critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)
  have hneighbor : l₃ ∈ Neighborhood ctx.Γ l₄ :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hl₄')
  have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core l₄ l₃ hneighbor
  exact hcore.trans (Subgroup.le_centralizer_iff.mp
    (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))))

private theorem source_odd_residual_conjugate_le_core_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (root : ctx.Γ.Vertex) (hcard : Nat.card (ZAt ctx.Γ root) = 2)
    (rootNeighbor : ctx.Γ.Vertex)
    (hrootNeighbor : rootNeighbor ∈ Neighborhood ctx.Γ root)
    (source : ctx.Γ.Vertex)
    (hsource : SourceOddW ctx.Γ source ≤ QAt ctx.Γ root)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ root) :
    SourceOddW ctx.Γ source ≤
      twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ root : Set G)) ⊔
        SourceOddW ctx.Γ (ctx.Γ.act actor source) := by
  have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    root rootNeighbor hrootNeighbor
  have hcentral : QAt ctx.Γ root ≤ Subgroup.centralizer (ZAt ctx.Γ root : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans
        (centerAmbient_le_centralizer _)))
  have hcommon : IsPGroup 2 (QAt ctx.Γ root) := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt root)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt ctx.Γ root)).map _
  have hresidual : EAt ctx.Γ root ≤ GAt ctx.Γ root := by
    change ctx.Γ.twoResidualAt root ≤ _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hnormalize := stabilizer_le_normalizer_q ctx.Γ root
    (hresidual ((EAt ctx.Γ root).inv_mem hactor))
  have hconjugate : (SourceOddW ctx.Γ source).conjBy actor⁻¹ ≤
      QAt ctx.Γ root := by
    exact (Subgroup.map_mono hsource).trans_eq
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalize)
  have hbound := nine_seven_order_two_residual_conjugate_bound ctx root hcard
    rootNeighbor hrootNeighbor (QAt ctx.Γ root) (SourceOddW ctx.Γ source)
    hcentral hcommon hsource actor⁻¹ ((EAt ctx.Γ root).inv_mem hactor) hconjugate
  rw [sup_comm, sourceOddW_act]
  exact hbound

public theorem nine_seven_source_initial_odd_setup
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
    : SourceInitialOddJoin ctx.Γ ctx.criticalPath.a ≤
        GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) ∧
      ⁅SourceInitialOddJoin ctx.Γ ctx.criticalPath.a,
        SourceInitialOddJoin ctx.Γ ctx.criticalPath.a⁆ = ⊥ := by
  refine ⟨?_, source_initial_odd_join_abelian ctx.toLocalContext ?_⟩
  rotate_left
  · change 8 < ctx.criticalPath.length
    obtain ⟨half, hhalf⟩ := (lemma_seven_five ctx.sectionSeven ctx.Γ
      ctx.criticalPath ctx.commutator_eq).odd_distance
    omega
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 7 < cp.length := hlong
  let second := cp.path ⟨2, by omega⟩
  let penultimate := cp.path ⟨cp.length - 1, by omega⟩
  let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
  let C := twoCoreIn (Subgroup.centralizer (R : Set G))
  have hthird : cp.path ⟨3, by omega⟩ = third := by
    obtain ⟨index, hindex, heq⟩ := hpath
    have hfin : index = ⟨3, by omega⟩ := Fin.ext hindex
    rwa [hfin] at heq
  have hfirstSecond : Γ.adjacent cp.firstStep second := by
    have hadj := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hadj
    rwa [cp.path_first] at hadj
  have hsecondThird : Γ.adjacent second third := by
    have hadj := cp.path_adj ⟨2, by omega⟩
    change Γ.adjacent second (cp.path ⟨3, by omega⟩) at hadj
    rwa [hthird] at hadj
  have hfirstNeThird : cp.firstStep ≠ third := by
    have hne := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first, hthird] at hne
  have hgeometry := nine_seven_commutator_geometry ctx hb third hpath hindex
    hfirstCard hfirstModel hendCard hendModel hstartData (by omega)
  have hRcard : Nat.card R = 2 := hgeometry.1
  obtain ⟨rho, hrho, hRrho⟩ := hgeometry.2.2.2.1
  have hroot := nine_seven_long_commutator_witness_on_path ctx hb third hpath hindex
    hfirstCard hfirstModel hendCard hendModel hstartData hlong rho hrho hRrho
  obtain ⟨orbitActor, horbitActor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    second ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstSecond)) hrho
  have hrhoOrbit : IsConjugateVertex Γ cp.firstStep rho := ⟨orbitActor, horbitActor⟩
  have htransport := nine_seven_residual_two_arc_transport ctx.toLocalContext hfirstModel
    (fun vertex horbit => (hstartData vertex horbit).1) rho hrhoOrbit
  have hCG : C ≤ GAt Γ penultimate :=
    (nine_seven_commutator_centralizer_core_control ctx hb third hpath hindex
      hfirstCard hfirstModel hendCard hendModel hstartData (by omega)).2.2.1
  have hQG : QAt Γ penultimate ≤ GAt Γ penultimate := by
    change Γ.twoCoreAt penultimate ≤ Γ.stabilizer penultimate
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  unfold SourceInitialOddJoin
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  have hsource : SourceOddW Γ neighbor ≤ QAt Γ rho := by
    apply source_odd_w_le_core_of_distance Γ cp
    have h₀ := nine_seven_adjacent_distance_bound Γ second rho rho
      ((mem_neighborhood_iff_adjacent Γ).mp hrho)
    rw [Γ.distance_refl] at h₀
    have h₁ := nine_seven_adjacent_distance_bound Γ cp.firstStep second rho hfirstSecond
    have h₂ := nine_seven_adjacent_distance_bound Γ cp.a cp.firstStep rho cp.firstStep_adj
    have h₃ := nine_seven_adjacent_distance_bound Γ neighbor cp.a rho
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
    omega
  have hbound (actor : G) (hactor : actor ∈ EAt Γ rho) :
      SourceOddW Γ neighbor ≤ C ⊔ SourceOddW Γ (Γ.act actor neighbor) := by
    have hrootNeighbor := (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hrho))
    have hres := source_odd_residual_conjugate_le_core_join ctx rho (hRrho ▸ hRcard)
      second hrootNeighbor neighbor hsource actor hactor
    rwa [← hRrho] at hres
  have hfinish (nearby : Γ.Vertex)
      (hcomparison : SourceOddW Γ neighbor ≤ C ⊔ SourceOddW Γ nearby)
      (hnearby : Γ.distance nearby penultimate ≤ cp.length - 4) :
      SourceOddW Γ neighbor ≤ GAt Γ penultimate := by
    apply hcomparison.trans (sup_le hCG ?_)
    exact (source_odd_w_le_core_of_distance Γ cp nearby penultimate
      (by omega)).trans hQG
  rcases hroot with hroot | hroot
  · rw [hroot] at htransport hbound
    by_cases hfirst : neighbor = cp.firstStep
    · subst neighbor
      unfold SourceOddW
      apply sSup_le
      rintro subgroup ⟨middle, hmiddle, endpoint, hendpoint, rfl⟩
      have hmiddleCore : GeneratedNeighborhoodV Γ middle ≤ QAt Γ cp.firstStep := by
        apply nine_seven_neighborhood_le_core_of_distance Γ cp
        have hdist := nine_seven_adjacent_distance_bound Γ middle cp.firstStep cp.firstStep
          (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hmiddle))
        rw [Γ.distance_refl] at hdist
        omega
      obtain ⟨actor, hactor, hmove⟩ := nine_seven_residual_neighbor_transitive
        ctx.sectionSeven Γ cp.firstStep middle second
        ((mem_neighborhood_iff_adjacent Γ).mp hmiddle) hfirstSecond
      have hcomparison := nine_seven_neighborhood_residual_conjugate_le_core_join ctx
        cp.firstStep (hroot ▸ hRrho ▸ hRcard) second
        ((mem_neighborhood_iff_adjacent Γ).mpr hfirstSecond) middle hmiddleCore actor hactor
      rw [hmove, ← hroot, ← hRrho] at hcomparison
      apply (show VAt Γ endpoint ≤ GeneratedNeighborhoodV Γ middle from
        le_sSup ⟨endpoint, hendpoint, rfl⟩).trans (hcomparison.trans (sup_le hCG ?_))
      apply (nine_seven_neighborhood_le_core_of_distance Γ cp second penultimate ?_).trans hQG
      have hdist := path_distance_le Γ cp 2 (cp.length - 1) (by omega) (by omega)
      change Γ.distance second penultimate ≤ cp.length - 1 - 2 at hdist
      omega
    obtain ⟨actor, hactor, _, hnearby⟩ := htransport cp.a neighbor second third
      (Γ.adjacent_symm cp.firstStep_adj)
      ((mem_neighborhood_iff_adjacent Γ).mp hneighbor) (Ne.symm hfirst)
      hfirstSecond hsecondThird hfirstNeThird
    have hdist := nine_seven_third_offset_nearby_bounds Γ cp hlong
    rw [hthird] at hdist
    apply hfinish third ?_ hdist.2
    exact hnearby ▸ hbound actor hactor
  · rw [hroot] at htransport hbound
    have hthirdFourth : Γ.adjacent third (cp.path ⟨4, by omega⟩) := by
      have hadj := cp.path_adj ⟨3, by omega⟩
      change Γ.adjacent (cp.path ⟨3, by omega⟩) _ at hadj
      rwa [hthird] at hadj
    have hfourthFifth : Γ.adjacent (cp.path ⟨4, by omega⟩) (cp.path ⟨5, by omega⟩) :=
      cp.path_adj ⟨4, by omega⟩
    have hthirdNeFifth : third ≠ cp.path ⟨5, by omega⟩ := by
      rw [← hthird]
      exact nine_seven_path_vertices_ne Γ cp 3 5 (by omega) (by omega)
    obtain ⟨actor, hactor, _, hnearby⟩ := htransport second cp.firstStep
      (cp.path ⟨4, by omega⟩) (cp.path ⟨5, by omega⟩)
      (Γ.adjacent_symm hsecondThird) (Γ.adjacent_symm hfirstSecond) hfirstNeThird.symm
      hthirdFourth hfourthFifth hthirdNeFifth
    have hfirstWalk : Γ.adjacent (Γ.act actor neighbor) (Γ.act actor cp.a) :=
      adjacent_act Γ actor (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
    have hsecondWalk : Γ.adjacent (Γ.act actor cp.a) (cp.path ⟨5, by omega⟩) := by
      rw [← hnearby]
      exact adjacent_act Γ actor cp.firstStep_adj
    exact hfinish (Γ.act actor neighbor) (hbound actor hactor)
      (nine_seven_fifth_offset_two_walk_nearby_bounds Γ cp hlong _ _ hfirstWalk hsecondWalk).2


end Stellmacher.SectionNine
