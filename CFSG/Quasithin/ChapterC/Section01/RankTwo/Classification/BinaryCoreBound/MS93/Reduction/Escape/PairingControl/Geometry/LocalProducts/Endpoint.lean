module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Algebra

/-!
# The edge supplement and endpoint noncontainment

At an M-vertex a, the radius group is Vcirc_a joined with the radius group
of any incident holomorph vertex. The local residual normalizes this join
by its defining commutator bound, while Q_a fixes the incident vertex.
Local transitivity then puts all radius-two generators in the join.

Apply this at the vertex two steps before a critical endpoint. The edge
layer three steps before the endpoint lies in Q_a by critical minimality.
If the moving group also lay in Q_a, the endpoint Z-layer would lie there,
contradicting reversal of the original critical pair.

Source: MS93 (1993), the argument for (4.3.1)(v)--(vi), p.883, and the
noncontainment reused at the end of (4.3.2), p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R}

omit [Finite M] in
theorem edge_radius_le_radius {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : V R t ≤ V R a := by
  apply V_le_of_h_neighbors ha hat
  intro d hdt
  apply le_iSup_of_le d
  apply le_iSup_of_le (show (cosetGraph R).dist d a ≤ 2 from ?_)
  · exact le_rfl
  · have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
    omega

theorem radius_eq_moving_sup_edge (source : LocalSource L R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    V R a = Vcirc R a ⊔ V R t := by
  have htV := edge_radius_le_radius ha hat
  have hn : stabilizer R a ≤ normalizer (Vcirc R a ⊔ V R t : Subgroup (FreeAmalgam R)) := by
    rw [← source.local_generation a ha]
    apply sup_le
    · exact normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
        (commutator_mono htV le_rfl)
    · exact (le_inf
        ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Vcirc_normalized a))
        ((show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans (V_normalized t))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm _ (sup_le (Vcirc_le_V a) htV)
  apply V_le_of_m_ball ha
  intro d hd hdist
  by_cases hda : d = a
  · subst d
    apply (show Z R a ≤ V R t from ?_).trans le_sup_right
    apply le_iSup_of_le a
    exact le_iSup_of_le
      (show (cosetGraph R).dist a t ≤ 2 from
        (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)).le.trans (by decide)) le_rfl
  have htwo : (cosetGraph R).dist a d = 2 := by
    have hne : (cosetGraph R).dist a d ≠ 0 := by
      intro hz
      exact hda ((cosetGraph_connected R).dist_eq_zero_iff.mp hz).symm
    have heven : Even ((cosetGraph R).dist a d) := by
      obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a d
      rw [← hw, walk_even_iff_color_eq, ha, hd]
    rw [Nat.even_iff] at heven
    rw [SimpleGraph.dist_comm] at hdist
    omega
  have hedist : (cosetGraph R).edist a d = 2 := by
    rw [← ((cosetGraph_connected R) a d).coe_dist_eq_edist, htwo]
    rfl
  obtain ⟨u, hau, hdu⟩ := (SimpleGraph.edist_eq_two_iff.mp hedist).2.2
  obtain ⟨g, hg, hgu⟩ := stabilizer_transitive_neighbors R a hat
    ((cosetGraph_adj R _ _).mp hau)
  have hVu : V R u ≤ Vcirc R a ⊔ V R t := by
    rw [← hgu, V_act]
    exact (map_mono (show V R t ≤ Vcirc R a ⊔ V R t from le_sup_right)).trans
      (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R a).inv_mem hg))).le
  apply (show Z R d ≤ V R u from ?_).trans hVu
  apply le_iSup_of_le d
  exact le_iSup_of_le
    (show (cosetGraph R).dist d u ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr hdu).le.trans (by decide)) le_rfl

theorem endpoint_moving_not_le (source : LocalSource L R) (p : Counterexample geometry)
    (hlarge : 6 < geometry.b R) : ¬ Vcirc R p.c ≤ Q R p.a := by
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  have hct : Adjacent R p.c t := adjacent_symm R
    (ht.adjacent (geometry := geometry) p.before)
  have htQ : V R t ≤ Q R p.a := by
    apply V_le_of_h_neighbors p.before_color hct
    intro d hdt
    have hd : color R d = false := by
      have htc := adjacent_color_ne R hct
      have htd := adjacent_color_ne R hdt
      rw [p.before_color] at htc
      cases hc : color R t <;> cases he : color R d <;> simp_all
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d p.a < geometry.b R
    have hdt' := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := p.a)
    have hpath := ht.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a)] at hpath
    omega
  intro h
  have hVc : V R p.c ≤ Q R p.a := by
    rw [radius_eq_moving_sup_edge source p.before_color hct]
    exact sup_le h htQ
  have hZ : Z R p.a' ≤ V R p.c := by
    apply le_iSup_of_le p.a'
    exact le_iSup_of_le (show (cosetGraph R).dist p.a' p.c ≤ 2 by
      rw [SimpleGraph.dist_comm, p.before.1]) le_rfl
  exact (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    (hZ.trans hVc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
