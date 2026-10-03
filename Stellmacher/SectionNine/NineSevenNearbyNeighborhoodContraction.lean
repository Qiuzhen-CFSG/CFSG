module

public import Stellmacher.SectionNine.NineSevenNeighborJoinBounds
public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# Nearby-neighborhood contraction reductions

Residual conjugates of an initial neighborhood are compared modulo the genuine
centralizer core by using the actual vertex two-core as their common two-group.
Rooted two-arc transport gives the required geometric contractions: in the
first-step branch the nonexceptional image is the third vertex; in the third
vertex branch the image is at most two edges from the fifth vertex. Both exact
source distance bounds are retained, including for backtracking two-edge walks.

The final reduction explicitly assumes rooted residual two-arc transport and
exceptional first-neighbor absorption. It is not the requested principal
`nine_seven_nearby_neighborhood_contraction`; those two upstream results remain
to be integrated. No unconditional contraction is asserted here.

Source: Stellmacher, printed p.54 / PDF p.44, first paragraph of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem nearby_adjacent_distance_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (left middle right : Γ.Vertex)
    (hadjacent : Γ.adjacent left middle) :
    Γ.distance left right ≤ Γ.distance middle right + 1 := by
  obtain ⟨tail, hstart, hend, hadj⟩ := Γ.distance_path middle right
  let path : Fin (Γ.distance middle right + 1 + 1) → Γ.Vertex := Fin.cases left tail
  have hpath : ∀ step : Fin (Γ.distance middle right + 1),
      Γ.adjacent (path step.castSucc) (path step.succ) := by
    intro step
    refine Fin.cases ?_ (fun next => ?_) step
    · change Γ.adjacent left (tail 0)
      rwa [hstart]
    · simpa [path] using hadj next
  have hbound := Γ.distance_le_of_path (Γ.distance middle right + 1) path hpath
  have hlast : path ⟨Γ.distance middle right + 1, Nat.lt_succ_self _⟩ = right := hend
  simpa only [show path 0 = left from rfl, hlast] using hbound

public theorem nine_seven_third_offset_nearby_bounds
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (hlong : 7 < cp.length) :
    Γ.distance (cp.path ⟨3, by omega⟩) cp.a' ≤ cp.length - 3 ∧
      Γ.distance (cp.path ⟨3, by omega⟩)
        (cp.path ⟨cp.length - 1, by omega⟩) ≤ cp.length - 4 := by
  constructor
  · have hbound := path_distance_le Γ cp 3 cp.length (by omega) le_rfl
    simpa only [cp.path_end] using hbound
  · have hbound := path_distance_le Γ cp 3 (cp.length - 1) (by omega) (by omega)
    convert hbound using 1
    omega

public theorem nine_seven_fifth_offset_two_walk_nearby_bounds
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (hlong : 7 < cp.length) (nearby middle : Γ.Vertex)
    (hfirst : Γ.adjacent nearby middle)
    (hsecond : Γ.adjacent middle (cp.path ⟨5, by omega⟩)) :
    Γ.distance nearby cp.a' ≤ cp.length - 3 ∧
      Γ.distance nearby (cp.path ⟨cp.length - 1, by omega⟩) ≤ cp.length - 4 := by
  have htail := path_distance_le Γ cp 5 cp.length (by omega) le_rfl
  rw [cp.path_end] at htail
  have hmiddle := nearby_adjacent_distance_bound Γ middle _ cp.a' hsecond
  have hnearby := nearby_adjacent_distance_bound Γ nearby middle cp.a' hfirst
  have htailPrevious := path_distance_le Γ cp 5 (cp.length - 1) (by omega) (by omega)
  have hmiddlePrevious := nearby_adjacent_distance_bound Γ middle _
    (cp.path ⟨cp.length - 1, by omega⟩) hsecond
  have hnearbyPrevious := nearby_adjacent_distance_bound Γ nearby middle
    (cp.path ⟨cp.length - 1, by omega⟩) hfirst
  constructor <;> omega

public theorem nine_seven_neighborhood_residual_conjugate_le_core_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (root : ctx.Γ.Vertex) (hcard : Nat.card (ZAt ctx.Γ root) = 2)
    (rootNeighbor : ctx.Γ.Vertex)
    (hrootNeighbor : rootNeighbor ∈ Neighborhood ctx.Γ root)
    (source : ctx.Γ.Vertex)
    (hsource : GeneratedNeighborhoodV ctx.Γ source ≤ QAt ctx.Γ root)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ root) :
    GeneratedNeighborhoodV ctx.Γ source ≤
      twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ root : Set G)) ⊔
        GeneratedNeighborhoodV ctx.Γ (ctx.Γ.act actor source) := by
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
  have hconjugate : (GeneratedNeighborhoodV ctx.Γ source).conjBy actor⁻¹ ≤
      QAt ctx.Γ root := by
    exact (Subgroup.map_mono hsource).trans_eq
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormalize)
  have hbound := nine_seven_order_two_residual_conjugate_bound ctx root hcard
    rootNeighbor hrootNeighbor (QAt ctx.Γ root) (GeneratedNeighborhoodV ctx.Γ source)
    hcentral hcommon hsource actor⁻¹ ((EAt ctx.Γ root).inv_mem hactor) hconjugate
  rw [sup_comm, nine_seven_neighborhood_act]
  exact hbound

public theorem nine_seven_initial_neighborhood_residual_conjugate_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlong : 7 < ctx.criticalPath.length) (root : ctx.Γ.Vertex)
    (hroot : root ∈ Neighborhood ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩))
    (hRroot : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ root)
    (hRcard : Nat.card
      (⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = 2)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ root) :
    GeneratedNeighborhoodV ctx.Γ neighbor ≤
      twoCoreIn (Subgroup.centralizer
        ((⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) : Set G)) ⊔
      GeneratedNeighborhoodV ctx.Γ (ctx.Γ.act actor neighbor) := by
  have hsource : GeneratedNeighborhoodV ctx.Γ neighbor ≤ QAt ctx.Γ root := by
    apply le_trans ?_ (nine_seven_initial_neighbor_join_le_neighbor_core
      ctx.toLocalContext (show 6 < ctx.criticalPath.length by omega) root hroot)
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hrootNeighbor := (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hroot))
  rw [hRroot]
  exact nine_seven_neighborhood_residual_conjugate_le_core_join ctx root
    (hRroot ▸ hRcard) _ hrootNeighbor neighbor hsource actor hactor

private theorem nearby_walk_distance_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (length : ℕ)
    (path : Fin (length + 1) → Γ.Vertex)
    (hadj : ∀ index : Fin length, Γ.adjacent (path index.castSucc) (path index.succ))
    (target : Γ.Vertex) :
    Γ.distance (path 0) target ≤ length + Γ.distance (path ⟨length, by omega⟩) target := by
  induction length with
  | zero => simp
  | succ length ih =>
    have htail := ih (fun index => path index.succ) (fun index => hadj index.succ)
    have hfirst := nearby_adjacent_distance_bound Γ (path 0) (path 1) target (hadj 0)
    change Γ.distance (path 1) target ≤
      length + Γ.distance (path ⟨length + 1, by omega⟩) target at htail
    omega

private theorem nearby_distance_triangle
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (first middle last : Γ.Vertex) :
    Γ.distance first last ≤ Γ.distance first middle + Γ.distance middle last := by
  obtain ⟨path, hfirst, hlast, hadj⟩ := Γ.distance_path first middle
  simpa only [hfirst, hlast] using
    nearby_walk_distance_bound Γ (Γ.distance first middle) path hadj last

public theorem nine_seven_path_vertices_ne
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (first last : ℕ) (hlt : first < last) (hbound : last ≤ cp.length) :
    cp.path ⟨first, by omega⟩ ≠ cp.path ⟨last, by omega⟩ := by
  intro heq
  have hprefix := path_distance_le Γ cp 0 first (by omega) (by omega)
  have htail := path_distance_le Γ cp last cp.length (by omega) le_rfl
  have hzero : (⟨0, by omega⟩ : Fin (cp.length + 1)) = 0 := Fin.ext rfl
  rw [hzero, cp.path_start, Nat.sub_zero, heq] at hprefix
  rw [cp.path_end] at htail
  have htriangle := nearby_distance_triangle Γ cp.a (cp.path ⟨last, by omega⟩) cp.a'
  rw [cp.endpoint_distance] at htriangle
  omega

public theorem nine_seven_nearby_contraction_of_rooted_two_arc
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlong : 7 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (root : ctx.Γ.Vertex) (hroot : root = ctx.criticalPath.firstStep ∨ root = third)
    (hRroot : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ root)
    (hRcard : Nat.card
      (⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = 2)
    (htransport : ∀ middle outer targetMiddle targetOuter : ctx.Γ.Vertex,
      ctx.Γ.adjacent root middle → ctx.Γ.adjacent middle outer → root ≠ outer →
      ctx.Γ.adjacent root targetMiddle → ctx.Γ.adjacent targetMiddle targetOuter →
      root ≠ targetOuter →
      ∃ actor : G, actor ∈ EAt ctx.Γ root ∧
        ctx.Γ.act actor middle = targetMiddle ∧ ctx.Γ.act actor outer = targetOuter)
    (hexceptional : root = ctx.criticalPath.firstStep →
      GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.firstStep ≤
        twoCoreIn (Subgroup.centralizer
          ((⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) : Set G)))
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    ∃ nearby : ctx.Γ.Vertex,
      GeneratedNeighborhoodV ctx.Γ neighbor ≤
        twoCoreIn (Subgroup.centralizer
          ((⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) : Set G)) ⊔
          GeneratedNeighborhoodV ctx.Γ nearby ∧
      ctx.Γ.distance nearby ctx.criticalPath.a' ≤ ctx.criticalPath.length - 3 ∧
      ctx.Γ.distance nearby (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) ≤
        ctx.criticalPath.length - 4 := by
  have hthird : ctx.criticalPath.path ⟨3, by omega⟩ = third := by
    obtain ⟨index, hindex, heq⟩ := hpath
    have hfin : index = ⟨3, by omega⟩ := Fin.ext hindex
    rwa [hfin] at heq
  have hfirstSecond : ctx.Γ.adjacent ctx.criticalPath.firstStep
      (ctx.criticalPath.path ⟨2, by omega⟩) := by
    have hadj := ctx.criticalPath.path_adj ⟨1, by omega⟩
    change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩) _ at hadj
    rwa [ctx.criticalPath.path_first] at hadj
  have hsecondThird : ctx.Γ.adjacent (ctx.criticalPath.path ⟨2, by omega⟩) third := by
    have hadj := ctx.criticalPath.path_adj ⟨2, by omega⟩
    change ctx.Γ.adjacent _ (ctx.criticalPath.path ⟨3, by omega⟩) at hadj
    rwa [hthird] at hadj
  have hfirstNeThird : ctx.criticalPath.firstStep ≠ third := by
    have hne := nine_seven_path_vertices_ne ctx.Γ ctx.criticalPath 1 3 (by omega) (by omega)
    rwa [ctx.criticalPath.path_first, hthird] at hne
  have hrootSecond : root ∈ Neighborhood ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    rcases hroot with rfl | rfl
    · exact ctx.Γ.adjacent_symm hfirstSecond
    · exact hsecondThird
  have hbound := nine_seven_initial_neighborhood_residual_conjugate_bound
    ctx hlong root hrootSecond hRroot hRcard neighbor hneighbor
  rcases hroot with hroot | hroot
  · subst root
    have hdist := nine_seven_third_offset_nearby_bounds ctx.Γ ctx.criticalPath hlong
    rw [hthird] at hdist
    by_cases heq : neighbor = ctx.criticalPath.firstStep
    · exact ⟨third, (heq ▸ hexceptional rfl).trans le_sup_left, hdist⟩
    · obtain ⟨actor, hactor, _, hnearby⟩ := htransport ctx.criticalPath.a neighbor
        (ctx.criticalPath.path ⟨2, by omega⟩) third
        (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor) (Ne.symm heq)
        hfirstSecond hsecondThird hfirstNeThird
      exact ⟨third, hnearby ▸ hbound actor hactor, hdist⟩
  · subst root
    have hthirdFourth : ctx.Γ.adjacent third (ctx.criticalPath.path ⟨4, by omega⟩) := by
      have hadj := ctx.criticalPath.path_adj ⟨3, by omega⟩
      change ctx.Γ.adjacent (ctx.criticalPath.path ⟨3, by omega⟩) _ at hadj
      rwa [hthird] at hadj
    have hfourthFifth : ctx.Γ.adjacent (ctx.criticalPath.path ⟨4, by omega⟩)
        (ctx.criticalPath.path ⟨5, by omega⟩) := ctx.criticalPath.path_adj ⟨4, by omega⟩
    have hthirdNeFifth : third ≠ ctx.criticalPath.path ⟨5, by omega⟩ := by
      rw [← hthird]
      exact nine_seven_path_vertices_ne ctx.Γ ctx.criticalPath 3 5 (by omega) (by omega)
    obtain ⟨actor, hactor, _, hnearby⟩ := htransport
      (ctx.criticalPath.path ⟨2, by omega⟩) ctx.criticalPath.firstStep
      (ctx.criticalPath.path ⟨4, by omega⟩) (ctx.criticalPath.path ⟨5, by omega⟩)
      (ctx.Γ.adjacent_symm hsecondThird) (ctx.Γ.adjacent_symm hfirstSecond)
      hfirstNeThird.symm hthirdFourth hfourthFifth hthirdNeFifth
    refine ⟨ctx.Γ.act actor neighbor, hbound actor hactor, ?_⟩
    apply nine_seven_fifth_offset_two_walk_nearby_bounds ctx.Γ ctx.criticalPath hlong
      _ (ctx.Γ.act actor ctx.criticalPath.a)
    · exact adjacent_act ctx.Γ actor
        (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))
    · rw [← hnearby]
      exact adjacent_act ctx.Γ actor ctx.criticalPath.firstStep_adj

end Stellmacher.SectionNine
