module

public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs

/-!
# Neighborhood estimates for the opening of Stellmacher (9.8)

For critical length greater than four, the join W of the neighbor V-groups
is abelian. At a neighbor of the first step, W lies in the stabilizer at
offset b-2. The terminal-center containment hypothesis also makes W
centralize the terminal center. These are local estimates only: neither
terminal-stabilizer containment nor the bound b ≤ 3 is asserted here.

Source: `refs/files/stellmacher-n-group.pdf`, printed p.55 / PDF p.45,
first paragraph of the proof of (9.8).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_eight_generated_neighborhood_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) (target : Subgroup G)
    (hcenters : ∀ middle ∈ neighborhood Γ vertex,
      ∀ endpoint ∈ neighborhood Γ middle, ZAt Γ endpoint ≤ target) :
    GeneratedNeighborhoodV Γ vertex ≤ target := by
  unfold GeneratedNeighborhoodV
  apply sSup_le
  rintro moduleGroup ⟨middle, hmiddle, rfl⟩
  rw [Γ.vAt_def]
  apply sSup_le
  rintro center ⟨endpoint, hendpoint, rfl⟩
  exact hcenters middle hmiddle endpoint hendpoint

public theorem nine_eight_v_le_generated_neighborhood
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) {vertex neighbor : Γ.Vertex}
    (hadj : neighbor ∈ neighborhood Γ vertex) :
    VAt Γ neighbor ≤ GeneratedNeighborhoodV Γ vertex := by
  exact le_sSup ⟨neighbor, hadj, rfl⟩

public theorem nine_eight_adjacent_distance_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) {start next target : Γ.Vertex}
    (hadj : Γ.adjacent start next) :
    Γ.distance start target ≤ Γ.distance next target + 1 := by
  obtain ⟨path, hstart, hend, hpath⟩ := Γ.distance_path next target
  let extended : Fin (Γ.distance next target + 1 + 1) → Γ.Vertex :=
    Fin.cases start path
  have hfirst : extended 0 = start := rfl
  have hlast : extended ⟨Γ.distance next target + 1, by omega⟩ = target := by
    exact hend
  have hextended : ∀ index : Fin (Γ.distance next target + 1),
      Γ.adjacent (extended index.castSucc) (extended index.succ) := by
    intro index
    refine Fin.cases ?_ (fun offset => ?_) index
    · change Γ.adjacent start (path 0)
      rwa [hstart]
    · exact hpath offset
  simpa [hfirst, hlast] using
    Γ.distance_le_of_path (Γ.distance next target + 1) extended hextended

public theorem nine_eight_neighborhood_abelian
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex) :
    IsMulCommutative (GeneratedNeighborhoodV ctx.Γ vertex) := by
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply nine_eight_generated_neighborhood_le
  intro leftMiddle hleftMiddle leftEndpoint hleftEndpoint
  apply Subgroup.le_centralizer_iff.mpr
  apply nine_eight_generated_neighborhood_le
  intro rightMiddle hrightMiddle rightEndpoint hrightEndpoint
  have hdist : ctx.Γ.distance leftEndpoint rightEndpoint ≤ 4 := by
    let path : Fin 5 → ctx.Γ.Vertex :=
      ![leftEndpoint, leftMiddle, vertex, rightMiddle, rightEndpoint]
    have hpath : ∀ index : Fin 4,
        ctx.Γ.adjacent (path index.castSucc) (path index.succ) := by
      intro index
      fin_cases index
      · exact ctx.Γ.adjacent_symm
          ((mem_neighborhood_iff_adjacent ctx.Γ).mp hleftEndpoint)
      · exact ctx.Γ.adjacent_symm
          ((mem_neighborhood_iff_adjacent ctx.Γ).mp hleftMiddle)
      · exact (mem_neighborhood_iff_adjacent ctx.Γ).mp hrightMiddle
      · exact (mem_neighborhood_iff_adjacent ctx.Γ).mp hrightEndpoint
    simpa [path] using ctx.Γ.distance_le_of_path 4 path hpath
  have hcore := critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)
  have hreverse : rightMiddle ∈ neighborhood ctx.Γ rightEndpoint :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hrightEndpoint))
  exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    rightEndpoint rightMiddle hreverse).trans
      ((omegaOneCenter_le_centerAmbient _).trans
        ((centerAmbient_le_centralizer _).trans (Subgroup.centralizer_le hcore)))

public theorem nine_eight_neighborhood_le_preterminal
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex)
    (hvertex : vertex ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep) :
    GeneratedNeighborhoodV ctx.Γ vertex ≤
      GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩) := by
  let cp := ctx.criticalPath
  have hbcp : 4 < cp.length := hb
  let previous := cp.path ⟨cp.length - 3, by omega⟩
  let next := cp.path ⟨cp.length - 2, by omega⟩
  have hcore : GeneratedNeighborhoodV ctx.Γ vertex ≤ QAt ctx.Γ previous := by
    apply nine_eight_generated_neighborhood_le
    intro middle hmiddle endpoint hendpoint
    have hvertexPath := neighbor_path_distance_le ctx.Γ cp vertex 1 (cp.length - 3)
      (by omega) (by omega) (by
        simpa [cp.path_first] using ctx.Γ.adjacent_symm
          ((mem_neighborhood_iff_adjacent ctx.Γ).mp hvertex))
    have hmiddlePath := nine_eight_adjacent_distance_le ctx.Γ (target := previous)
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hmiddle))
    have hendpointPath := nine_eight_adjacent_distance_le ctx.Γ (target := previous)
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hendpoint))
    apply critical_minimality ctx.Γ cp
    change ctx.Γ.distance vertex previous ≤ cp.length - 3 - 1 + 1 at hvertexPath
    have hlength : 4 < cp.length := hb
    omega
  have hadj : next ∈ neighborhood ctx.Γ previous := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hedge := cp.path_adj ⟨cp.length - 3, by omega⟩
    have hindex : (⟨cp.length - 3, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 2, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex] at hedge
    exact hedge
  exact hcore.trans
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core previous next hadj default).2.2

public theorem nine_eight_neighborhood_centralizes_terminal_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (vertex : ctx.Γ.Vertex)
    (hvertex : vertex ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep) :
    GeneratedNeighborhoodV ctx.Γ vertex ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a' : Set G) := by
  have hreverse : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ vertex :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hvertex))
  have hle := hcontain.trans (nine_eight_v_le_generated_neighborhood ctx.Γ hreverse)
  exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr
    (nine_eight_neighborhood_abelian ctx hb vertex)).trans (Subgroup.centralizer_le hle)

end Stellmacher.SectionNine
