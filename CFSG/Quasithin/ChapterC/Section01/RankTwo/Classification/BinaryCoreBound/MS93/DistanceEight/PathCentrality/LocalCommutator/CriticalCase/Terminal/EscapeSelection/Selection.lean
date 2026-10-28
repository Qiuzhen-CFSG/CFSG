module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Fixedness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.SmallAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source

/-!
# Selecting lambda from an escaping radius-two displacement

A displacement has order at most four. If its join with the central Z-layer
were normal in the local stabilizer, the small-section action theorem for
the genuine SL3(2) quotient would put it in B. An escaping displacement
therefore gives a nonnormal join, normal in the local kernel. The backward
critical endpoint normally generates modulo that kernel, so a conjugate of
the join fails to be normalized by its Z-layer. Its conjugated vertex is the
actual lambda of TerminalNeighbor, with exact distance two retained.

This proves the selection once an escaping rho is supplied. The preceding
all-rho-in-B contradiction on the same page is still required to discharge
that premise; no unconditional TerminalNeighbor constructor is asserted.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.1)(vii), pp.855--856, and (4.4.1), p.892 after claim (3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

private theorem displacement_join_le_kernel
    (hb : 2 < geometry.b R)
    {rho c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist c rho = 2) :
    ⁅Z R rho, Q R c⁆ ⊔ Z R c ≤ Q R c := by
  have hrho : color R rho = false :=
    (color_eq_of_dist_even R c rho (by rw [hd]; decide)).symm.trans hc
  have hZ : Z R rho ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R rho (geometry.exists_critical _ hrho)
    rw [geometry.distance_constant _ hrho, SimpleGraph.dist_comm, hd]
    exact hb
  apply sup_le
  · exact (commutator_mono hZ le_rfl).trans (le_normalizer_iff_commutator_le_right.mp (Q R c).le_normalizer)
  · exact (Z_le_VBall R c 2).trans (geometry.V_le_Q hb c hc)

omit [Finite M] in
private theorem displacement_join_kernel_normal
    {rho c : Vertex R} :
    ((⁅Z R rho, Q R c⁆ ⊔ Z R c).subgroupOf (Q R c)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (le_inf (normalizer_commutator_ge_right _ _)
    ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (Z_normalized R c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A small displacement escaping B cannot have a normal join with Z. -/
theorem displacement_join_nonnormal
    (common : CommonFacts R source geometry) (hb : 2 < geometry.b R)
    {rho c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist c rho = 2)
    (he : ¬ ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ¬ ((⁅Z R rho, Q R c⁆ ⊔ Z R c).subgroupOf (stabilizer R c)).Normal := by
  intro hn
  let S := stabilizer R c
  let E := ⁅Z R rho, Q R c⁆
  let J := E ⊔ Z R c
  have hJQ : J ≤ Q R c := displacement_join_le_kernel hb hc hd
  have hJS : J ≤ S := hJQ.trans (fun _ hx => hx.1)
  have hES : E ≤ S := le_sup_left.trans hJS
  let := finite_stabilizer R c
  let J₀ := J.subgroupOf S
  let Z₀ := (Z R c).subgroupOf S
  let E₀ := E.subgroupOf S
  let : J₀.Normal := hn
  let : Z₀.Normal := geometry.Z_normal c
  obtain ⟨π, hπ, hπker⟩ := Escape.Initial.Natural.exists_localProjection source c hc
  have hp : IsPGroup 2 π.ker := by
    rw [hπker]
    exact (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
  have hcard : Nat.card E₀ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv]
    exact displacement_card_le_four common
      ((color_eq_of_dist_even R c rho (by rw [hd]; decide)).symm.trans hc)
      (by rwa [SimpleGraph.dist_comm])
  have hsmall : Z₀.relIndex J₀ ≤ 4 := by
    have heq : J₀ = E₀ ⊔ Z₀ := subgroupOf_sup hES (Z_le_stabilizer R c)
    rw [heq, relIndex_sup_right]
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card Z₀ E₀)).trans hcard
  have hcomm := Escape.Propagation.Backward.Moving.Symmetry.small_normal_section_residual
    π hπ hp J₀ Z₀ (fun _ hx => (show Z R c ≤ J from le_sup_right) hx)
    (by rw [hπker]; exact fun _ hx => hJQ hx) hsmall
  have hcomm' : ⁅J, Ltilde R c⁆ ≤ Z R c := by
    have hm := map_mono (f := S.subtype) hcomm
    rwa [map_commutator, map_subgroupOf_eq_of_le hJS,
      map_subgroupOf_eq_of_le (Z_le_stabilizer R c)] at hm
  apply he
  apply (le_B_iff hb hc E).mpr
  refine ⟨?_, (commutator_mono le_sup_left le_rfl).trans hcomm'⟩
  apply (commutator_mono ?_ le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans
        (DistanceEight.V_normalized R c)))
  exact le_iSup_of_le rho (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hd]) le_rfl)

/-- An escaping displacement at the predecessor supplies the actual lambda,
by relative normal generation. -/
theorem terminalNeighbor_of_escape_at_predecessor
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (w : BackwardWitness R geometry a c)
    (he : ∃ rho, (cosetGraph R).dist w.predecessor rho = 2 ∧
      ¬ ⁅Z R rho, Q R w.predecessor⁆ ≤
        B R w.predecessor (geometry.Z_normal w.predecessor)) :
    Nonempty (TerminalNeighbor w) := by
  obtain ⟨rho, hd, hn⟩ := he
  let J := ⁅Z R rho, Q R w.predecessor⁆ ⊔ Z R w.predecessor
  have hJQ : J ≤ Q R w.predecessor :=
    displacement_join_le_kernel (by omega) w.predecessor_color hd
  have hN : ¬ (J.subgroupOf (stabilizer R w.predecessor)).Normal :=
    displacement_join_nonnormal common (by omega) w.predecessor_color hd hn
  let p := (w.shifted ha (by omega : 2 ≤ geometry.b R)).reverse common
  have hgen := Escape.Initial.local_conjugate_generation source w.predecessor
    w.predecessor_color (Z R w.backward) (p.endpoint_Z_le_start_stabilizer (by omega))
      (w.shifted ha (by omega)).critical.2
  obtain ⟨g, hg, hmove, _⟩ := NormalizerTransfer.simultaneous_escape
    (Z R w.backward) (stabilizer R w.predecessor) (Q R w.predecessor) J J
    (fun _ hx => hx.1) hJQ hJQ displacement_join_kernel_normal
    displacement_join_kernel_normal hN hN hgen
  have hfix : act R g w.predecessor = w.predecessor := hg
  refine ⟨⟨act R g rho, ?_, ?_⟩⟩
  · rw [← hfix, dist_act]
    exact hd
  · have heq : NormalizerTransfer.rightConjugate J g =
        ⁅Z R (act R g rho), Q R w.predecessor⁆ ⊔ Z R w.predecessor := by
      simp only [NormalizerTransfer.rightConjugate, J, Subgroup.map_sup, map_commutator,
        ← Z_act, ← Q_act, hfix]
    rwa [heq] at hmove

/-- The all-rho contradiction at the original center is the only remaining
premise of the lambda selection. -/
theorem terminalNeighbor_of_escape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (w : BackwardWitness R geometry a c)
    (he : ∃ rho, (cosetGraph R).dist c rho = 2 ∧
      ¬ ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    Nonempty (TerminalNeighbor w) :=
  terminalNeighbor_of_escape_at_predecessor common hb ha w
    (escape_at_any_center (by omega) w.path.start_color w.predecessor_color he)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
