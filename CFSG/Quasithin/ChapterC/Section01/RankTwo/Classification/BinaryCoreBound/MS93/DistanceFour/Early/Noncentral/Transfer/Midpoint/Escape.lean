module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Contracts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.LocalAction

/-!
# Escape from the kernel of a distinct midpoint conjugate

Suppose the radius group at d lies in the kernel at its conjugate d'. The
Z-layer at d' is then central in the radius at d, so (4.6.1) puts it in B_d.
Select the actual marked parabolic whose two-core is the edge kernel. Its
two-residual normalizes the displacement of this neighboring Z-layer: the
B-commutator lies in Z_d and residual idempotence sharpens that bound to the
index-two edge layer. These are the relative normalization statements proved
in `Escape.Propagation.Rigidity.LocalAction`.

The marked natural decomposition gives the residual's moving plane and
identifies its fixed part with the local center. A normalized noncentral
four-group is its own residual commutator, hence is the original edge plane.
The critical line lies in every midpoint conjugate plane and has trivial
intersection with the center at d. Thus the conjugate plane is noncentral,
and the preceding equality contradicts its choice as a distinct plane.

The proof retains right conjugation and the original fixed-preimage B. It
uses the preceding center containment and edge facts, with the actual module
structure supplied by `Initial.moduleFacts`; it does not need a later radius
center identity or a core classification.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the first conjugate comparison in the second (4.6.6), pp.903--904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
open Initial Flags.RankOne
open Escape.Propagation.Rigidity.LocalAction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual edge residual forces every noncentral displacement of a
neighboring Z-layer in B to be the original natural plane. -/
private theorem nonmoving_plane_eq_base
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d : Vertex R) (hdb : Adjacent R d (beta R))
    (hB : Z R d ≤ B R (alpha R) (geometry.Z_normal _))
    (hn : ¬ ⁅Z R d, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ⁅Z R d, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  have hi := edge.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  obtain ⟨i, hkernel⟩ := select_flag_kernel source geometry (moduleFacts common) hi
    (edge.edge_Q_index (alpha R) (beta R) rfl (base_adjacent R))
  have hcard := edge.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  obtain ⟨hmove, hfixed⟩ := edgeFixedLayerAction source geometry common.large_distance
    (moduleFacts common)
    (edge.edge_commutator_le_Z (alpha R) (beta R) rfl (base_adjacent R)) hcard hi i hkernel
  let D := ⁅Z R d, Q R (beta R)⁆
  let H := flagResidual source i
  have hd : color R d = false := by
    have hh := adjacent_color_ne R hdb
    have hb : color R (beta R) = true := rfl
    cases hc : color R d <;> simp_all
  have hDZ : D ≤ Z R (beta R) := edge.edge_commutator_le_Z d (beta R) hd hdb
  have hDcard : Nat.card D = 4 := edge.edge_commutator_card d (beta R) hd hdb
  have hnorm : H ≤ normalizer D :=
    nonmoving_displacement_normalized common.large_distance i hkernel hi d hdb hB
  have hDP : D ≤ flagParabolic source i :=
    (hDZ.trans (show Z R (beta R) ≤ Q R (beta R) from omegaCenter_le _)).trans
      (hkernel ▸ flagKernel_le source i)
  have hne : ⁅D,H⁆ ≠ ⊥ := by
    intro heq
    exact hn ((le_inf hDZ (commutator_eq_bot_iff_le_centralizer.mp heq)).trans hfixed)
  have hidem := flag_two_idempotent source i D hDP (IsPGroup.of_card (n := 2) hDcard) hnorm
  have heq := (MarkedAction.moving_four_fixed_free D D H hDcard hnorm
    (le_normalizer_iff_commutator_le_left.mp hnorm) hne hidem).1
  have hle : D ≤ ⁅Z R (alpha R), Q R (beta R)⁆ := by
    change ⁅Z R (beta R), H⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ at hmove
    rw [← hmove, ← heq]
    exact commutator_mono hDZ le_rfl
  let : Finite (⁅Z R (alpha R), Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact eq_of_le_of_card_ge hle (by rw [hDcard, hcard])

/-- Transport the marked calculation to the literal pair of adjacent vertices. -/
theorem nonmoving_plane_eq
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : Z R d ≤ B R a (geometry.Z_normal a))
    (hn : ¬ ⁅Z R d, Q R b⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    ⁅Z R d, Q R b⁆ = ⁅Z R a, Q R b⁆ := by
  obtain ⟨g, hga, hgb⟩ := Escape.Propagation.exists_edge_transport ha
    (show color R (alpha R) = false from rfl) hab (base_adjacent R)
  change act R g b = beta R at hgb
  have hd : Adjacent R (act R g d) (beta R) :=
    hgb ▸ (adjacent_act_iff R g d b).mpr hdb
  have hB' : Z R (act R g d) ≤ B R (alpha R) (geometry.Z_normal _) := by
    rw [← hga, Escape.PairingControl.FirstPairing.B_act common.large_distance g a ha, Z_act]
    exact map_mono hB
  have hcenter : (center (stabilizer R (act R g a))).map
      (stabilizer R (act R g a)).subtype =
      ((center (stabilizer R a)).map (stabilizer R a).subtype).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    rw [stabilizer_act, ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective]
  have hn' : ¬ ⁅Z R (act R g d), Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
    rw [← hga, ← hgb, hcenter, Z_act, Q_act, ← map_commutator,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
    exact hn
  have heq := nonmoving_plane_eq_base common edge (act R g d) hd hB' hn'
  rw [← hga, ← hgb, Z_act, Z_act, Q_act, ← map_commutator, ← map_commutator] at heq
  exact (Subgroup.map_injective (MulAut.conj g⁻¹).injective) heq

/-- The first comparison in the second MS93 (4.6.6): the radius escapes the
kernel of every midpoint-edge conjugate with a distinct displacement plane. -/
theorem conjugateEscape
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry) (edge : EdgeFacts R) :
    ConjugateEscape geometry := by
  intro d e c b hd hcrit hdc hce hdb hcb hcentral _hnot h hhc hhb hne hcontained
  have hhb' : act R h b = b := hhb
  have hdb' : Adjacent R (act R h d) b := by
    simpa only [hhb'] using (adjacent_act_iff R h d b).mpr hdb
  have hd' : color R (act R h d) = false := (action_preserves_color R h d).trans hd
  have hdist : (cosetGraph R).dist (act R h d) d ≤ 2 := by
    have ht := (cosetGraph_connected R).dist_triangle (u := act R h d) (v := b) (w := d)
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb')
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdb))
    omega
  have hZV : Z R (act R h d) ≤ V R d :=
    le_iSup_of_le (act R h d) (le_iSup_of_le hdist le_rfl)
  have hZcenter : Z R (act R h d) ≤ (center (V R d)).map (V R d).subtype := by
    intro x hx
    refine ⟨⟨x, hZV hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes (act R h d) hd')) hx y (hcontained y.property))
  have hB := hZcenter.trans (initial.center_le_B d hd)
  have hn : ¬ ⁅Z R (act R h d), Q R b⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
    intro hfix
    have hline := critical_line_le_conjugate_plane common hb d e c b hd hcrit hdc hce
      hcb hcentral h hhc hhb
    have hlineP := critical_line_le_edge_and_midpoint_center common hb d e c b hd hcrit
      hdc hce hcb hcentral
    have hzero : ⁅Z R d, Z R e⁆ = ⊥ := le_bot_iff.mp
      ((le_inf (hlineP.trans inf_le_left) (hline.trans hfix)).trans
        (edge_plane_inf_center common d b hd hdb).le)
    have hc := critical_line_card common d e hd hcrit
    have hc1 := card_eq_one.mpr hzero
    omega
  exact hne (nonmoving_plane_eq common edge d b (act R h d) hd hdb hdb' hB hn)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
