module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Basic

/-!
# Far propagation from moving symmetry

These are the two assertions of (4.3.7)(iii), conditional on the preceding
symmetry assertion (ii). A normal radius product at the vertex four before
the endpoint would put the endpoint Z-layer in the centralizer of the
starting Z-layer, contradicting the critical commutator's order two.

For the radius bound, the resulting nonmoving Z-product is normal at the
vertex four before the endpoint. Conjugate its second generator towards the
start. The moving radius product centralizes both new generators by critical
minimality, hence centralizes the original Z-product. The local centralizer
identity then puts it in the kernel two before the endpoint. No normality of
the radius product at that far vertex is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(iii), printed p.888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- A reverse-moving far pair contradicts the nontrivial critical
commutator. The product input is used at d through genuine transport. -/
theorem far_reverse_not_moving (p : Counterexample geometry)
    (hb : 6 < geometry.b R) (initial : InitialFacts p)
    (products : ProductFacts geometry) {d : Vertex R} (hd : Before p.a p.a' d 4) :
    d ∉ movingNeighbors geometry p.c := by
  intro hm
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hcd : (cosetGraph R).dist p.c d = 2 := by
    rw [SimpleGraph.dist_comm]
    exact before_dist (geometry := geometry) hd p.before (by decide)
  have hda : (cosetGraph R).dist d p.a + 2 < geometry.b R := by
    have h := hd.2
    rw [p.distance_eq_b] at h
    rw [SimpleGraph.dist_comm]
    omega
  have hp := products_at p (by omega) products d p.c hdc (by
    rw [SimpleGraph.dist_comm]; exact hcd) hm
  have hV : V R p.c ≤ Q R p.a := le_sup_left.trans
    (normal_radius_product_le_kernel p.before_color hdc hcd (by omega) hp.2.1 hda)
  have hZ : Z R p.a' ≤ V R p.c :=
    le_iSup_of_le p.a' (le_iSup_of_le (show (cosetGraph R).dist p.a' p.c ≤ 2 by
      rw [SimpleGraph.dist_comm, p.before.1]) le_rfl)
  have hcomm : criticalCommutator p.a p.a' = ⊥ := by
    apply le_bot_iff.mp
    change ⁅Z R p.a, Z R p.a'⁆ ≤ ⊥
    rw [← geometry.centralizes p.a p.color_a]
    exact commutator_mono le_rfl (hZ.trans hV)
  have hcard := initial.critical_card
  rw [hcomm] at hcard
  simp at hcard

/-- Symmetry at the transported far vertex turns the reverse exclusion
into the literal first assertion of (iii). -/
theorem far_not_moving_of_symmetric (p : Counterexample geometry)
    (hb : 6 < geometry.b R) (initial : InitialFacts p)
    (products : ProductFacts geometry)
    (symmetric : ∀ q : Counterexample geometry, ∀ e,
      e ∈ movingNeighbors geometry q.a ↔ q.a ∈ movingNeighbors geometry e)
    {d : Vertex R} (hd : Before p.a p.a' d 4) :
    p.c ∉ movingNeighbors geometry d := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) d hdc
  have hs := symmetric q p.c
  rw [hq] at hs
  exact fun hm => far_reverse_not_moving p hb initial products hd (hs.mp hm)

/-- Once the far pair is nonmoving, the radius bound follows from normal
products and a local conjugator. This does not assume moving symmetry. -/
theorem radius_bound_of_far_not_moving (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 6 < geometry.b R)
    {d e : Vertex R} (hd : Before p.a p.a' d 4)
    (hne : p.c ∉ movingNeighbors geometry d)
    (he : (cosetGraph R).dist p.a e = 2)
    (hn : ((V R e ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal) :
    V R e ≤ Q R p.c := by
  have hec : color R e = false :=
    (color_eq_of_dist_even R p.a e (he.symm ▸ (by decide : Even 2))).symm.trans p.color_a
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hcd : (cosetGraph R).dist p.c d = 2 := by
    rw [SimpleGraph.dist_comm]
    exact before_dist (geometry := geometry) hd p.before (by decide)
  have hda : (cosetGraph R).dist d p.a + 4 = geometry.b R := by
    rw [SimpleGraph.dist_comm]
    exact hd.2.trans p.distance_eq_b
  have hprod (v : Vertex R) (hv : (cosetGraph R).dist p.a v + 2 < geometry.b R) :
      V R e ⊔ V R p.a ≤ Q R v :=
    normal_radius_product_le_kernel hec p.color_a (by rw [SimpleGraph.dist_comm]; exact he)
      (by omega) hn hv
  have hAd : V R e ⊔ V R p.a ≤ Q R d := hprod d (by
    rw [SimpleGraph.dist_comm]; omega)
  obtain ⟨t, hct, hdt⟩ := exists_common_neighbor_of_dist_two R p.c d hcd
  obtain ⟨u, hdu, hua⟩ := exists_adjacent_dist_sub_one R d p.a (by omega)
  obtain ⟨g, hgd, hgt⟩ := stabilizer_transitive_neighbors R d hdt hdu
  have hcgu : Adjacent R (act R g p.c) u := by
    rw [← hgt]
    exact (adjacent_act_iff R g p.c t).mpr hct
  have hcga : (cosetGraph R).dist p.a (act R g p.c) + 2 < geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle
      (u := act R g p.c) (v := u) (w := p.a)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcgu)
    rw [SimpleGraph.dist_comm (u := p.a)]
    omega
  have hAcg := hprod (act R g p.c) hcga
  have hnB := nonmoving_Z_join_normalized source (by omega) hdc
    (by rw [SimpleGraph.dist_comm]; exact hcd) hne
  have hmap := mem_normalizer_iff_map_conj_eq.mp
    (hnB ((stabilizer R d).inv_mem hgd))
  change (Z R d ⊔ Z R p.c).map (MulAut.conj g⁻¹).toMonoidHom = Z R d ⊔ Z R p.c at hmap
  have hfix : act R g d = d := hgd
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hfix] at hmap
  have hcentral : Z R d ⊔ Z R p.c ≤
      centralizer (V R e ⊔ V R p.a : Subgroup (FreeAmalgam R)) := by
    rw [← hmap]
    exact sup_le
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)).trans
        (centralizer_le hAd))
      ((commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes (act R g p.c) (by rw [action_preserves_color]; exact p.before_color))).trans
        (centralizer_le hAcg))
  have hAlocal : V R e ⊔ V R p.a ≤ stabilizer R p.c :=
    hAd.trans (Q_le_stabilizer_of_dist_le_two d p.c hdc p.before_color (by
      rw [SimpleGraph.dist_comm]; exact hcd.le))
  have hAC : V R e ⊔ V R p.a ≤ C R p.c :=
    le_inf hAlocal (le_centralizer_iff.mp (le_sup_right.trans hcentral))
  rw [source.C_eq_Q geometry.radical_ne_bot p.c p.before_color] at hAC
  exact le_sup_left.trans hAC

/-- The second assertion of (iii), with only (ii) still explicit. -/
theorem radius_bound_of_symmetric (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 6 < geometry.b R) (initial : InitialFacts p)
    (products : ProductFacts geometry)
    (symmetric : ∀ q : Counterexample geometry, ∀ e,
      e ∈ movingNeighbors geometry q.a ↔ q.a ∈ movingNeighbors geometry e)
    {e : Vertex R} (he : e ∈ movingNeighbors geometry p.a) : V R e ≤ Q R p.c := by
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  exact radius_bound_of_far_not_moving source p hb hd
    (far_not_moving_of_symmetric p hb initial products symmetric hd) he.1
    (products.products p e he.1 ((symmetric p e).mp he)).2.1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
