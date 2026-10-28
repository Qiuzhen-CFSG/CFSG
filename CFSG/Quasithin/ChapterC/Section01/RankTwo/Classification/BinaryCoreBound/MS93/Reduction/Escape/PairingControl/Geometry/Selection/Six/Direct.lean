module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Direct.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay

/-!
# The contained six-step contradiction

Assume R₀ <= Z_middle on the actual selected path with positions
1, 2, 3, 4, 5. Direct.Incidence constructs the genuine native seed from the
critical endpoint's faithful action. Direct.Pairing applies (1.7)(ii) in
G_c, including the intrinsic natural centralizer quotient, and identifies
R₁ = [Z_a,V_c] with the actual c-choice edge plane and first middle plane.

The selected centralizer equality gives Q_middle = Q_c. Every Z-layer in
the middle ball therefore lies in the pairing actor and centralizes V_choice.t.
Its commutator with V_c is either trivial or R₁. Apply the proved source
neighbor-generation display at the middle vertex, relative to the first edge.
For an eligible neighbor, movement bounds that value by a different edge
plane; nonmovement bounds it by the disjoint fixed core. Both exclude R₁.
Thus every eligible neighbor radius centralizes Z_a′ and lies in Q_a′ by
the faithful natural endpoint action. The display forces V_middle <= Q_a′,
and hence Z_a <= Q_a′, contradicting the original critical pair.

This replaces the printed moving-mu selection by its full generating-family
argument. It retains the same path and CentralizerChoice, and uses no later
local-control, propagation, or escape conclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.2)(4)--(5), printed pp.884--885, and (1.7)(ii), pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
open TerminalPairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- Every Z-layer in the middle ball centralizes the prescribed choice radius. -/
theorem middle_ball_centralizes_choice (path : Selection.SixPath p)
    (choice : CentralizerChoice p) {d : Vertex R} (hd : color R d = false)
    (hdm : (cosetGraph R).dist d path.middle ≤ 2) :
    Z R d ≤ centralizer (V R choice.t : Set (FreeAmalgam R)) := by
  apply le_centralizer_iff.mpr
  apply le_trans ?_ (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)))
  apply Initial.Consequences.V_le_of_h_neighbors path.middle_color
    (path.middle_choice_adjacent choice)
  intro e het
  have he : color R e = false := by
    have h₁ := adjacent_color_ne R (path.middle_choice_adjacent choice)
    have h₂ := adjacent_color_ne R het
    have hm := path.middle_color
    cases ht : color R choice.t <;> cases he : color R e <;> simp_all
  apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
  rw [geometry.distance_constant e he]
  change (cosetGraph R).dist e d < geometry.b R
  rw [path.six]
  have htri₁ := (cosetGraph_connected R).dist_triangle (u := e) (v := choice.t) (w := path.middle)
  have htri₂ := (cosetGraph_connected R).dist_triangle (u := e) (v := path.middle) (w := d)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr het),
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R (path.middle_choice_adjacent choice)))] at htri₁
  rw [SimpleGraph.dist_comm (u := path.middle) (v := d)] at htri₂
  omega

/-- The faithful natural endpoint action turns centrality into kernel containment. -/
theorem middle_ball_Z_le_endpoint_of_central (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (path : Selection.SixPath p)
    {d : Vertex R} (hd : color R d = false)
    (hdm : (cosetGraph R).dist d path.middle ≤ 2)
    (hz : ⁅V R p.c, Z R d⁆ = ⊥) : Z R d ≤ Q R p.a' := by
  rw [← modules.natural.centralizer p.a' p.end_color]
  apply le_inf
  · apply geometry.Z_le_stabilizer_of_dist_le_b d hd p.a'
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := path.middle) (w := p.a')
    rw [path.middle_before.1, path.six] at *
    omega
  · apply (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
    apply centralizer_le
    apply (U_le_Z p.a').trans
    exact le_iSup_of_le p.a' (le_iSup_of_le (by rw [SimpleGraph.dist_comm, p.before.1]) le_rfl)

/-- The printed R₁ is both the actual choice-edge plane at c and the first
middle-edge plane. The constructed seed and pairing are explicit here. -/
theorem source_R1_eq_edges (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle)
    (edge : EdgeSeedAt source p.c choice.t p.before_color) (pair : edge.Pairing) :
    ⁅Z R p.a, V R p.c⁆ = edgeDisplacement p.c choice.t ∧
      edgeDisplacement p.c choice.t = edgeDisplacement path.middle path.first := by
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  have hQ := path.middle_kernel_eq_predecessor source choice hcontained
  have hC := middle_ball_centralizes_choice path choice p.color_a path.start_middle_distance.le
  have hD : Z R p.a ≤ Q R p.c := (Z_le_VBall R p.a 2).trans p.trapped
  have he : ⁅V R p.c, Z R p.a⁆ = edgeDisplacement p.c choice.t := by
    rcases full_pairing_dichotomy source hb modules initial facts bad p.before_color
      (adjacent_symm R (SixPath.choice_predecessor_adjacent choice)) edge pair _ hD hC with hz | hv
    · exact (p.critical.2 (middle_ball_Z_le_endpoint_of_central source modules path p.color_a
        path.start_middle_distance.le hz)).elim
    · exact hv
  refine ⟨(commutator_comm _ _).trans he, ?_⟩
  have hle : edgeDisplacement p.c choice.t ≤ edgeDisplacement path.middle path.first := by
    rw [← he, commutator_comm, ← path.start_commutator_eq_edge source modules initial facts bad]
    exact commutator_mono le_rfl path.predecessor_V_le_middle_kernel
  let := finite_stabilizer R path.middle
  let : Finite (edgeDisplacement path.middle path.first) := Finite.of_injective
    (inclusion ((Initial.edge_le_natural source _ _ path.middle_color
      (adjacent_symm R path.first_middle_adjacent)).trans
      ((U_le_Z path.middle).trans (Z_le_stabilizer R path.middle)))) (inclusion_injective _)
  apply eq_of_le_of_card_ge hle
  rw [FirstPairing.StepThree.edge_card p (by omega) initial p.c choice.t p.before_color
    (adjacent_symm R (SixPath.choice_predecessor_adjacent choice)),
    FirstPairing.StepThree.edge_card p (by omega) initial path.middle path.first
      path.middle_color (adjacent_symm R path.first_middle_adjacent)]

/-- The contained branch of (4.3.2)(5), with the seed and every pairing premise
discharged on the original selected six-step path. -/
theorem false_of_radius_le_middle_Z (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle) : False := by
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  obtain ⟨edge⟩ := edge_at_choice_of_contained source modules initial facts bad choice path hcontained
  obtain ⟨pair⟩ := EdgeSeedAt.pairing_of_local_facts source geometry hb facts edge
  have hR1 := (source_R1_eq_edges source modules initial facts bad choice path hcontained edge pair).2
  have hQ := path.middle_kernel_eq_predecessor source choice hcontained
  have hct := adjacent_symm R (SixPath.choice_predecessor_adjacent choice)
  have hmfirst := adjacent_symm R path.first_middle_adjacent
  have hspan : V R path.middle ≤ Q R p.a' := by
    rw [Centralizer.Generation.source_neighbor_generation source hb modules initial facts p
      path.middle_color hmfirst]
    apply iSup_le
    intro s
    apply iSup_le
    intro hms
    apply iSup_le
    intro hs
    apply Initial.Consequences.V_le_of_h_neighbors path.middle_color hms
    intro d hds
    have hd : color R d = false := by
      have h₁ := adjacent_color_ne R hms
      have h₂ := adjacent_color_ne R hds
      have hm := path.middle_color
      cases ht : color R s <;> cases hd : color R d <;> simp_all
    have hdm : (cosetGraph R).dist d path.middle ≤ 2 := by
      have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := s) (w := path.middle)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds),
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hms))] at ht
      exact ht
    by_cases heq : d = path.middle
    · subst d
      exact path.middle_Z_le_end_kernel
    have hdist : (cosetGraph R).dist path.middle d = 2 := by
      have hlow := (cosetGraph_connected R).one_lt_dist_of_ne_of_not_adj (Ne.symm heq) (by
        intro hadj
        exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp hadj)) (path.middle_color.trans hd.symm))
      rw [SimpleGraph.dist_comm] at hdm
      omega
    have hD : Z R d ≤ Q R p.c := by
      rw [← hQ]
      have hZV : Z R d ≤ V R path.middle :=
        le_iSup_of_le d (le_iSup_of_le hdm le_rfl)
      exact hZV.trans (geometry.V_le_Q hb path.middle path.middle_color)
    have hC := middle_ball_centralizes_choice path choice hd hdm
    apply middle_ball_Z_le_endpoint_of_central source modules path hd hdm
    rcases full_pairing_dichotomy source hb modules initial facts bad p.before_color
      hct edge pair _ hD hC with hz | hv
    · exact hz
    exfalso
    have hvalue : edgeDisplacement path.middle path.first ≤ ⁅Z R d, Q R path.middle⁆ := by
      rw [← hR1, ← hv, commutator_comm]
      exact commutator_mono le_rfl path.predecessor_V_le_middle_kernel
    by_cases hfixed : Z R d ≤ B R path.middle (geometry.Z_normal path.middle)
    · have hbound := hvalue.trans (EdgeSeed.fixed_neighbor_commutator_le_fixedCore source hb
        modules facts path.middle_color hd hdist hfixed)
      have hbot : edgeDisplacement path.middle path.first = ⊥ := by
        apply le_bot_iff.mp
        apply le_trans (le_inf (Initial.edge_le_natural source _ _ path.middle_color hmfirst)
          (hbound.trans inf_le_right))
        exact (EdgeTransfer.U_fixed_eq_bot modules path.middle path.middle_color).le
      exact EdgeTransfer.edge_commutator_ne_bot modules _ _ path.middle_color hmfirst hbot
    · have hmoving : d ∈ movingNeighbors geometry path.middle := ⟨hdist, hfixed⟩
      rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
        initial bad path.middle s d path.middle_color hms hds hmoving,
        facts.edge_eq path.middle s d path.middle_color hms hds hmoving] at hvalue
      have hne := Centralizer.Generation.SourceDisplay.edges_distinct_of_centralizer_eq source hb
        modules facts path.middle_color hmfirst hs
      apply hne
      let := finite_stabilizer R path.middle
      let : Finite (edgeDisplacement path.middle s) := Finite.of_injective
        (inclusion ((Initial.edge_le_natural source _ _ path.middle_color hms).trans
          ((U_le_Z path.middle).trans (Z_le_stabilizer R path.middle)))) (inclusion_injective _)
      apply eq_of_le_of_card_ge hvalue
      rw [FirstPairing.StepThree.edge_card p (by omega) initial path.middle path.first path.middle_color hmfirst,
        FirstPairing.StepThree.edge_card p (by omega) initial path.middle s path.middle_color hms]
  exact p.critical.2 (path.start_Z_le_middle_V.trans hspan)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Direct
