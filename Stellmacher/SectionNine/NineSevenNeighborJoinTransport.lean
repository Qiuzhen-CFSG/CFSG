module
public import Stellmacher.SectionNine.NineSevenLongWitnessLocalization
public import Stellmacher.SectionNine.NineSevenNearbyNeighborhoodContraction
public import Stellmacher.SectionNine.NineSevenTerminalContainedHelpers

/-!
# Initial neighbor-join containment at the penultimate vertex

Under the order-eight module and SL₂(2) quotient data of (9.7), at critical
distance greater than seven the join of neighborhoods at all initial neighbors
lies in the penultimate vertex stabilizer. This is the containment required by
the terminal normality cases.

The actual critical commutator has an order-two center witness near offset
two, and the localization theorem puts that witness at the first or third
path vertex. Rooted residual transport compares every nonexceptional source
neighborhood with a nearby neighborhood modulo the centralizer two-core.
Critical minimality puts the nearby neighborhood in the penultimate core.
For the exceptional first neighbor, the production neighborhood equals its
module, which already lies in the penultimate core by the first extraction
bound. Thus the conclusion requires no additional absorption hypothesis.

Source: Stellmacher (9.7), printed p.54 / PDF p.44, first paragraph, ending
with the inclusion of U in the penultimate stabilizer. The proof retains
the repository's uniform definition of GeneratedNeighborhoodV.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_seven_initial_neighbor_join_le_penultimate
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
    : sSup {subgroup : Subgroup G | ∃ neighbor,
        neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
          subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤
      GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) := by
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
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  by_cases hfirst : neighbor = cp.firstStep
  · rw [nine_seven_neighbor_neighborhood_eq_module ctx neighbor hneighbor, hfirst]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1.trans hQG
  have hbound := nine_seven_initial_neighborhood_residual_conjugate_bound ctx hlong
    rho hrho hRrho hRcard neighbor hneighbor
  have hfinish (nearby : Γ.Vertex)
      (hcomparison : GeneratedNeighborhoodV Γ neighbor ≤ C ⊔ GeneratedNeighborhoodV Γ nearby)
      (hnearby : Γ.distance nearby penultimate ≤ cp.length - 4) :
      GeneratedNeighborhoodV Γ neighbor ≤ GAt Γ penultimate := by
    apply hcomparison.trans (sup_le hCG ?_)
    exact (nine_seven_neighborhood_le_core_of_distance Γ cp nearby penultimate
      (by omega)).trans hQG
  rcases hroot with hroot | hroot
  · rw [hroot] at htransport hbound
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
