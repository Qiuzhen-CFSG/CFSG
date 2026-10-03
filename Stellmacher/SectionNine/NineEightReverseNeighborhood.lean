module
public import Stellmacher.SectionNine.NineEightTerminalContainment
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization

/-!
# The symmetric neighborhood containment in Stellmacher (9.8)

Suppose the first-step center lies in the terminal module and an extracted
terminal-neighbor center escapes the initial stabilizer. Every neighborhood
join W at a terminal neighbor then lies in the first-step stabilizer.
No bound from (9.8) or unfinished (9.7) is assumed.

The escaping center is outside the first-step core. Critical minimality
and the tail path make that neighbor and the first-step vertex a critical
pair, with the terminal vertex as prescribed first neighbor. Their centers
commute inside the elementary terminal module. Prescribed-edge normalization
therefore gives a genuine ambient Section Nine context with the same
critical length. Apply the proved W terminal containment there and transport
back through the actual graph conjugation.

Source: Stellmacher (9.8), printed p.55/PDF p.45, the paragraph beginning
with the symmetric first-step/terminal-center containment.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem neighborhood_le_of_commuting_critical_pair
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (left right next : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hadj : ctx.Γ.adjacent left next)
    (hdistance : ctx.Γ.distance left right = ctx.Γ.distance next right + 1)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ = ⊥)
    (hcontain : ZAt ctx.Γ right ≤ VAt ctx.Γ next)
    (vertex : ctx.Γ.Vertex) (hvertex : vertex ∈ Neighborhood ctx.Γ next) :
    GeneratedNeighborhoodV ctx.Γ vertex ≤ GAt ctx.Γ right := by
  obtain ⟨actor, path, hleft, hright, hnext, hlength⟩ :=
    exists_criticalPath_of_critical_pair_through_neighbor ctx.sectionSeven
      ctx.Γ ctx.criticalPath left right next hcritical hadj hdistance
  have hpathComm : ⁅ctx.Γ.z path.a, ctx.Γ.z path.a'⁆ = ⊥ := by
    rw [hleft,hright,z_act,z_act,← Subgroup.map_commutator]
    change (⁅ZAt ctx.Γ left,ZAt ctx.Γ right⁆).map _ = ⊥
    rw [hcomm,Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := path, commutator_eq := hpathComm }
  have hpathContain : ZAt ctx.Γ path.a' ≤ VAt ctx.Γ path.firstStep := by
    change z ctx.Γ path.a' ≤ v ctx.Γ path.firstStep
    rw [hright,hnext,z_act,v_act]
    exact Subgroup.map_mono hcontain
  have hvertexPath : ctx.Γ.act actor vertex ∈ Neighborhood ctx.Γ path.firstStep := by
    rw [hnext]
    exact (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (adjacent_act ctx.Γ actor ((mem_neighborhood_iff_adjacent ctx.Γ).mp hvertex))
  have hbound := nine_eight_neighborhood_le_terminal shifted
    (by change 3 < path.length; rwa [hlength]) hpathContain
    (ctx.Γ.act actor vertex) hvertexPath
  change GeneratedNeighborhoodV ctx.Γ (ctx.Γ.act actor vertex) ≤ GAt ctx.Γ path.a' at hbound
  rw [nine_seven_neighborhood_act,hright] at hbound
  change (GeneratedNeighborhoodV ctx.Γ vertex).map _ ≤ stabilizer ctx.Γ (ctx.Γ.act actor right) at hbound
  rw [stabilizer_act] at hbound
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hbound

public theorem nine_eight_reverse_neighborhood_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hreverse : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a')
    (hescape : ¬ ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a)
    (vertex : ctx.Γ.Vertex) (hvertex : vertex ∈ Neighborhood ctx.Γ ctx.criticalPath.a') :
    GeneratedNeighborhoodV ctx.Γ vertex ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlong : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hnot : ¬ ZAt Γ neighbor ≤ QAt Γ cp.firstStep := by
    intro hle
    exact hescape (hle.trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      cp.firstStep cp.a ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm cp.firstStep_adj)) default).2.2))
  have htail : Γ.distance cp.a' cp.firstStep ≤ cp.length - 1 := by
    have hpath := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [Γ.distance_symm]
    simpa only [cp.path_first,cp.path_end] using hpath
  have hadj : Γ.adjacent neighbor cp.a' := Γ.adjacent_symm
    ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
  have hupper := nine_eight_adjacent_distance_le Γ hadj (target := cp.firstStep)
  have hlower : cp.length ≤ Γ.distance neighbor cp.firstStep := by
    by_contra hlt
    exact hnot (critical_minimality Γ cp (by omega))
  have hdistance : Γ.distance neighbor cp.firstStep = cp.length := by omega
  have hcritical : IsCriticalPair Γ neighbor cp.firstStep := by
    refine ⟨?_,hnot⟩
    rw [hdistance,← cp.endpoint_distance]
    exact cp.critical.1
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hlong).2.2.1
  have hcomm : ⁅ZAt Γ neighbor,ZAt Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hneighborV.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le hreverse)))
  exact neighborhood_le_of_commuting_critical_pair ctx hb neighbor cp.firstStep cp.a'
    hcritical hadj (by change Γ.distance neighbor cp.firstStep = Γ.distance cp.a' cp.firstStep + 1; omega) hcomm hreverse vertex hvertex

end Stellmacher.SectionNine
