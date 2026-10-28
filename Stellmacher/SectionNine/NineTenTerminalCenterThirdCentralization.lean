module

public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineEightNeighborhood

/-!
# A retained terminal neighbor center fixes the third module

For any terminal neighbor, the module at the third critical-path vertex
lies in that neighbor's core. Indeed, each center generating the third
module has distance at most b−2 from the terminal vertex and at most b−1
from the neighbor. Critical minimality supplies every required containment.
The edge center-core theorem then makes the retained neighbor center
centralize the entire third module.

This is the actor-centralization hypothesis in the application of (9.4)
inside Stellmacher (9.10), printed p.57. It uses the actual path offset and
terminal neighbor and requires no support decomposition or pending (9.4)
conclusion. In fact, existence of the third offset already gives the only
length bound needed for this local geometric calculation.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

public theorem nine_ten_terminal_neighbor_center_centralizes_third
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (third neighbor : ctx.Γ.Vertex)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a') :
    ZAt ctx.Γ neighbor ≤ Subgroup.centralizer (VAt ctx.Γ third : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change IsCriticalPathOffset Γ cp 3 third at hthird
  have hadj : Γ.adjacent neighbor cp.a' :=
    Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hVcore : VAt Γ third ≤ QAt Γ neighbor := by
    rw [VAt, v, Γ.vAt_def]
    apply sSup_le
    rintro center ⟨vertex, hvertex, rfl⟩
    obtain ⟨index, hindex, rfl⟩ := hthird
    have hlength : 3 ≤ cp.length := by omega
    have hindexEq : index = ⟨3, by omega⟩ := Fin.ext hindex
    have hvertexAdj := Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hvertex)
    rw [hindexEq] at hvertexAdj
    have hpath := neighbor_path_distance_le Γ cp vertex 3 cp.length
      hlength le_rfl hvertexAdj
    rw [cp.path_end] at hpath
    have hstep := nine_eight_adjacent_distance_le Γ (target := vertex) hadj
    rw [Γ.distance_symm neighbor vertex, Γ.distance_symm cp.a' vertex] at hstep
    exact critical_minimality Γ cp (by omega)
  have hreverse : cp.a' ∈ neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr hadj
  have hcenter : ZAt Γ neighbor ≤ Subgroup.centralizer (QAt Γ neighbor : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core neighbor cp.a' hreverse).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  exact hcenter.trans (Subgroup.centralizer_le hVcore)

end Stellmacher.SectionNine
