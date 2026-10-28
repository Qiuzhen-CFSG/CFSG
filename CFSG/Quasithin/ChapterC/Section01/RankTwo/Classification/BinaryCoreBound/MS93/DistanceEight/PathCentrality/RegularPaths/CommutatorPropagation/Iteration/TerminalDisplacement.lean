module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Commutator

/-!
# The terminal natural displacement in MS93 (4.4.4)

The seed's terminal edge contains the nontrivial critical commutator. Since
that commutator lies in Z_a and the seed does not, the containment is strict.
Lagrange's theorem and the edge bound of four therefore give order four for
the seed; no edge-plane equality is assumed.

Once the literal failed-span commutator K lies in U_(a+2), it has index two
there. The terminal radius group centralizes K and normalizes U_(a+2), so
its action on the quotient of order two is trivial. The central summand of
Z_(a+2) contributes no displacement. We reuse the proved general plane
lemma from Reduction/Escape/Propagation/Backward/Bound/Commutator, whose
hypotheses require only ModuleFacts, not a contrary configuration.

This supplies the displacement implication consumed by
Iteration.Conclusion.contradiction_of_local_steps. Its hU premise remains
with the backward-iteration assembly owner; the proof uses neither the
recurrence nor the final contradiction. The literal inverse conjugation
is retained in failedSpanCommutator.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the final paragraph of (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

private theorem terminal_adjacent (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
  have hb := common.large_distance
  have hlen := p.length_eq_b
  have hh := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
  rw [show p.walk.length - 1 + 1 = p.walk.length by omega,
    SimpleGraph.Walk.getVert_length] at hh
  exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)

/-- The terminal edge properly contains the nontrivial critical commutator,
so the seed has order four. No plane hypothesis is added. -/
theorem terminal_seed_card_four [Finite M] (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {K : Subgroup (FreeAmalgam R)} (seed : TerminalPropagationSeed p K) :
    Nat.card K = 4 := by
  have hb := common.large_distance
  have hlen := p.length_eq_b
  have ht := terminal_adjacent common p
  have hKU : K ≤ U R a' := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural hb
      (moduleFacts common) a' _ p.end_color ht
  let := finite_stabilizer R a'
  let : Finite K := Finite.of_injective
    (inclusion (hKU.trans ((U_le_Z R a').trans (Z_le_stabilizer R a'))))
    (inclusion_injective _)
  let C := ⁅Z R a, Z R a'⁆
  have hZQ : Z R a ≤ Q R (p.walk.getVert (p.walk.length - 1)) := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a p.start_color)
    rw [geometry.distance_constant a p.start_color, p.dist_start (by omega)]
    change p.walk.length - 1 < geometry.b R
    omega
  have hCK : C ≤ K := by
    rw [seed.terminal_edge, edgeCommutator]
    exact (commutator_mono hZQ le_rfl).trans_eq (commutator_comm _ _)
  let : Finite C := Finite.of_injective (inclusion hCK) (inclusion_injective _)
  have hCZ : C ≤ Z R a := le_normalizer_iff_commutator_le_left.mp
    ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a))
  have hpos : 1 < Nat.card C := (one_lt_card_iff_ne_bot C).mpr
    (common.critical_noncommutation a p.start_color a' p.critical)
  have hlt : Nat.card C < Nat.card K := by
    by_contra! hh
    have heq : C = K := eq_of_le_of_card_ge hCK hh
    exact seed.not_le_start_Z (heq ▸ hCZ)
  obtain ⟨k, hk⟩ := card_dvd_of_le hCK
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  have hfour : 4 ≤ Nat.card K := by nlinarith
  have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four hb
    (moduleFacts common) a' _ p.end_color ht
  change Nat.card (edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))) ≤ 4 at hsmall
  rw [← seed.terminal_edge] at hsmall
  omega

/-- The last natural-module implication in MS93 (4.4.4), for the literal
failed-span commutator. Its containment in the second natural layer is the
separate output of the backward iteration. -/
theorem terminal_displacement [Finite M] (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') {g : FreeAmalgam R}
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hU : failedSpanCommutator p g ≤ U R (p.walk.getVert 2)) :
    ⁅Z R (p.walk.getVert 2), V R a'⁆ ≤ failedSpanCommutator p g := by
  have hb := common.large_distance
  have hlen := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hVS : V R a' ≤ stabilizer R (p.walk.getVert 2) := by
    apply (V_le_iff R p.end_color _).mpr
    intro d hd hda
    apply geometry.Z_le_stabilizer_of_dist_le_b d hd
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a')
      (w := p.walk.getVert 2)
    rw [SimpleGraph.dist_comm (u := a'), p.dist_end 2] at htri
    omega
  have hKU : failedSpanCommutator p g ≤ U R a' := by
    rw [seed.terminal_edge]
    exact Escape.EdgeTransfer.edge_commutator_le_natural hb
      (moduleFacts common) a' _ p.end_color (terminal_adjacent common p)
  have hVK : V R a' ≤ centralizer (failedSpanCommutator p g : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    exact (hKU.trans (U_le_Z R a')).trans
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a' p.end_color)).trans
        (centralizer_le (geometry.V_le_Q hb a' p.end_color)))
  exact Escape.Propagation.Backward.natural_plane_commutator_le source hb (moduleFacts common)
    _ hc _ _ hU (terminal_seed_card_four common p seed) hVS hVK

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
