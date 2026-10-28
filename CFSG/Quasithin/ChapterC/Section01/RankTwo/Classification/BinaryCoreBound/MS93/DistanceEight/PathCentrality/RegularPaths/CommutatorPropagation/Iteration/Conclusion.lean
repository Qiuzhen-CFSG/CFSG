module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Recurrence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.FixedDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor

/-!
# The final escape contradiction, conditional on two local calculations

The terminal edge is proper in U_(a'). A bound for [Z_(a+2),V_(a')] by that
edge therefore forces this commutator to vanish, by (4.4.1). The faithful
natural action puts V_(a') in Q_(a+2), contradicting reversed (4.3).

The final theorem combines this argument with the four-step induction.
Its edge-switching and terminal-displacement premises remain explicit;
this module is not yet an unconditional proof of the source (4.4.4).

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The literal final displacement bound contradicts (4.3): (4.4.1) kills it
at a', and faithfulness of the natural action puts V_(a') in Q_(a+2). -/
theorem contradiction_of_terminal_displacement [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hbound : ⁅Z R (p.walk.getVert 2), V R a'⁆ ≤ K) : False := by
  have hlen := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph R).dist (p.walk.getVert 2) a' = p.walk.length - 2 := p.dist_end 2
  have hA : Z R (p.walk.getVert 2) ≤ Q R a' := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc, hdist]
    change p.walk.length - 2 < geometry.b R
    omega
  have ht : Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
    rw [show p.walk.length - 1 + 1 = p.walk.length by omega,
      SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have hKU : K ≤ U R a' := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ p.end_color ht
  have hproper : K ≠ U R a' := by
    intro he
    have hcard := Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) _ _ p.end_color ht
    change Nat.card (edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))) ≤ 4 at hcard
    rw [← seed.terminal_edge, he, common.natural.card_at a' p.end_color] at hcard
    omega
  have hzero : ⁅V R a', Z R (p.walk.getVert 2)⁆ = ⊥ :=
    radius_displacement_eq_bot common hlocal p.end_color hA hKU hproper
      (by rwa [commutator_comm])
  have hVS : V R a' ≤ stabilizer R (p.walk.getVert 2) := by
    apply (V_le_iff R p.end_color _).mpr
    intro d hd hda
    apply geometry.Z_le_stabilizer_of_dist_le_b d hd
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a')
      (w := p.walk.getVert 2)
    rw [SimpleGraph.dist_comm (u := a'), hdist] at htri
    omega
  have hVQ : V R a' ≤ Q R (p.walk.getVert 2) := by
    apply le_kernel_of_normalizes_incident common hc hVS
    intro t ht
    have hE : edgeCommutator R (p.walk.getVert 2) t ≤ Z R (p.walk.getVert 2) :=
      (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (moduleFacts common) _ _ hc ht).trans (U_le_Z R _)
    exact ((commutator_eq_bot_iff_le_centralizer.mp hzero).trans (centralizer_le hE)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply common.escape a' p.end_color a (p.reverse common).critical (p.walk.getVert 2)
    (by rw [SimpleGraph.dist_comm, p.dist_start (by omega)]) _ hVQ
  rw [SimpleGraph.dist_comm (u := a'), hdist, SimpleGraph.dist_comm (u := a'), ← p.shortest]
  omega

/-- Final assembly with the two local natural-action implications left
explicit. This is a conditional reduction, not yet the source theorem. -/
theorem contradiction_of_local_steps [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K)
    (hswitch : BackwardEdgeSwitching p K)
    (hdisplacement : K ≤ U R (p.walk.getVert 2) →
      ⁅Z R (p.walk.getVert 2), V R a'⁆ ≤ K) : False :=
  contradiction_of_terminal_displacement common hb hlocal p seed
    (hdisplacement (le_second_natural_of_switching common hb p hp seed hswitch))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
