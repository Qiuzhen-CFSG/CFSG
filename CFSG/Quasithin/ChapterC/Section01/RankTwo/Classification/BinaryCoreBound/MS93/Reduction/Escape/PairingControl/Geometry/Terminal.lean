module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths

/-!
# Edge centralization from the local normal product

Suppose the moving groups at alpha and alpha+2 have a normal product in
G_(alpha+2). Conjugating the first edge towards a specified far vertex
shortens the distance of the alpha-side factor. Both conjugate factors then
lie in that vertex's kernel by critical minimality. Normality transfers this
bound to the original product. Applying it to every M-neighbor of alpha'-3
proves the edge centralization used on p.886.

The endpoint-side moving group is local at alpha by distance alone. Thus the
normal-product result and its noncontainment in Q_alpha suffice to construct
the literal TerminalSeed. Those two inputs are still explicit here.

Source: MS93 (1993), (4.3.2), the end of p.885 and start of p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- Actual local conjugation moves the first edge towards d; no transitivity
on distance-two vertices, nor equality of their Z-layers, is assumed. -/
theorem normal_product_le_kernel {a s d : Vertex R}
    (ha : color R a = false) (hs : color R s = false)
    (has : (cosetGraph R).dist a s = 2) (hb : 4 < geometry.b R)
    (hn : ((Vcirc R a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal)
    (hd : (cosetGraph R).dist s d + 2 < geometry.b R) :
    Vcirc R a ⊔ Vcirc R s ≤ Q R d := by
  by_cases hds : d = s
  · subst d
    apply sup_le
    · exact (Vcirc_le_V a).trans (V_le_Q_of_distance ha (by omega))
    · exact (Vcirc_le_V s).trans (V_le_Q_of_distance hs hd)
  have hlocal : Vcirc R a ⊔ Vcirc R s ≤ stabilizer R s := by
    apply sup_le
    · exact (Vcirc_le_V a).trans (V_le_stabilizer_of_distance ha (by omega))
    · exact (Vcirc_le_V s).trans (V_le_stabilizer_of_distance hs (by simp; omega))
  have hnorm := (normal_subgroupOf_iff_le_normalizer hlocal).mp hn
  obtain ⟨t, hat, hst⟩ := exists_common_neighbor_of_dist_two R a s has
  have hpos : 0 < (cosetGraph R).dist s d :=
    (cosetGraph_connected R).pos_dist_of_ne (Ne.symm hds)
  obtain ⟨u, hsu, hud⟩ := exists_adjacent_dist_sub_one R s d hpos
  obtain ⟨g, hgs, hgt⟩ := stabilizer_transitive_neighbors R s hst hsu
  have hgu : Adjacent R (act R g a) u := by
    rw [← hgt]
    exact (adjacent_act_iff R g a t).mpr hat
  have hag : color R (act R g a) = false := by rw [action_preserves_color]; exact ha
  have hgd : (cosetGraph R).dist (act R g a) d + 2 < geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := act R g a) (v := u) (w := d)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hgu)
    omega
  have hmap := mem_normalizer_iff_map_conj_eq.mp
    (hnorm ((stabilizer R s).inv_mem hgs))
  change (Vcirc R a ⊔ Vcirc R s).map (MulAut.conj g⁻¹).toMonoidHom =
    Vcirc R a ⊔ Vcirc R s at hmap
  have hfix : act R g s = s := hgs
  rw [Subgroup.map_sup, ← Vcirc_act, ← Vcirc_act, hfix] at hmap
  rw [← hmap]
  exact sup_le ((Vcirc_le_V _).trans (V_le_Q_of_distance hag hgd))
    ((Vcirc_le_V s).trans (V_le_Q_of_distance hs hd))

/-- The forward normal product centralizes the full V-layer at alpha'-3. -/
theorem edge_centralizes_of_forward_normal (p : Counterexample geometry)
    (hb : 6 < geometry.b R) {s t : Vertex R}
    (hs : Before p.a' p.a s 2) (ht : Before p.a p.a' t 3)
    (hn : ((Vcirc R p.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal) :
    ⁅Vcirc R p.a, V R t⁆ = ⊥ := by
  have hsc : color R s = false := (hs.color (by decide)).trans p.color_a
  have has : (cosetGraph R).dist p.a s = 2 := by rw [SimpleGraph.dist_comm]; exact hs.1
  have hsf : Before p.a p.a' s (geometry.b R - 2) := by
    have h := before_reverse hs
    rwa [SimpleGraph.dist_comm (u := p.a'), p.distance_eq_b] at h
  have hst := before_distance (geometry := geometry) hsf ht (by omega)
  have hct : Adjacent R p.c t := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  apply V_le_of_h_neighbors p.before_color hct
  intro d hdt
  have hdc : color R d = false := by
    have htc : color R t = true := by
      have hh := adjacent_color_ne R hct
      rw [p.before_color] at hh
      cases h : color R t <;> simp_all
    have hh := adjacent_color_ne R hdt
    cases h : color R d <;> simp_all
  have hsd : (cosetGraph R).dist s d + 2 < geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := s) (v := t) (w := d)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))
    omega
  have hkernel : Vcirc R p.a ≤ Q R d := le_sup_left.trans
    (normal_product_le_kernel p.color_a hsc has (by omega) hn hsd)
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)).trans
    (centralizer_le hkernel)

/-- The endpoint-side moving group is in G_alpha even before any pairing. -/
theorem actor_local (p : Counterexample geometry) : Vcirc R p.c ≤ stabilizer R p.a := by
  apply (Vcirc_le_V p.c).trans
  apply V_le_stabilizer_of_distance p.before_color
  rw [SimpleGraph.dist_comm]
  have h := p.before.2
  rw [p.distance_eq_b] at h
  exact h.le

/-- The remaining local-normality and noncontainment inputs produce an actual
terminal witness, with its chosen three-step predecessor and incident edge. -/
noncomputable def terminalSeed_of_forward_normal (p : Counterexample geometry)
    (hb : 6 < geometry.b R) {s : Vertex R} (hs : Before p.a' p.a s 2)
    (hn : ((Vcirc R p.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal)
    (hout : ¬ Vcirc R p.c ≤ Q R p.a) : TerminalSeed p := by
  classical
  let witness := p.exists_before (show 3 ≤ geometry.b R by omega)
  let t := witness.choose
  have ht : Before p.a p.a' t 3 := witness.choose_spec
  exact {
    t := t
    before := ht
    adjacent := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
    six_lt := hb
    edge_centralizes := edge_centralizes_of_forward_normal p hb hs ht hn
    actor_local := actor_local p
    actor_not_le := hout }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
