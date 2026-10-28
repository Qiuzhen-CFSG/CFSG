module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Commutator

/-!
# The radius/H identification in MS93 (4.3.6)

The endpoint of the critical pair is a moving neighbor of the vertex c two
steps before it. Otherwise the quotient-fixed definition of B_c bounds its
Z-layer's residual commutator by Z_c. The kernel already normalizes both
Z-layers, so local residual/kernel generation normalizes their join. A local
conjugator moves the last edge toward the starting vertex, putting both
Z-layers strictly within the critical distance. Invariance of the join would
then put the original endpoint layer in the starting kernel, contradicting
the reversed critical pair.

The endpoint's edge displacement is therefore H_c by (4.3.2). The actual
last-edge identity from (4.3.1) identifies that displacement with R₀. Neither
noncentrality at the vertex four before the endpoint nor a radius-product
normality or moving-symmetry assertion is needed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.1)--(4.3.2), and the first paragraph of (4.3.6), printed p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Radius
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The critical endpoint moves at c: a nonmoving Z-layer would have a
locally invariant join with Z_c, which can be conjugated inside Q_a. -/
theorem endpoint_moving (source : LocalSource L R) (p : Counterexample geometry)
    (hb : 2 < geometry.b R) : p.a' ∈ movingNeighbors geometry p.c := by
  refine ⟨p.before.1, ?_⟩
  intro hB
  have hcomm : ⁅Z R p.a', Ltilde R p.c⁆ ≤ Z R p.c := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R p.c (geometry.Z_normal p.c)
      ((geometry.V_le_Q hb p.c p.before_color).trans (fun _ hv => hv.1)) x).mp
        (hB hx)).2 l hl
  have hnorm : stabilizer R p.c ≤
      normalizer (Z R p.c ⊔ Z R p.a' : Subgroup (FreeAmalgam R)) := by
    rw [← source.local_generation p.c p.before_color]
    apply sup_le
    · exact PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer p.c).trans (Z_normalized R p.c)) hcomm
    · exact (le_inf
        ((show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1).trans
          (Z_normalized R p.c))
        ((Q_le_stabilizer_of_dist_two R p.c p.a' p.before_color p.before.1).trans
          (Z_normalized R p.a'))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  have hcs : Adjacent R p.c s := p.before.adjacent (geometry := geometry) hs
  have hct : Adjacent R p.c t := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.c hcs hct
  have hgt : Adjacent R (act R g p.a') t := by
    rw [← hgs]
    exact (adjacent_act_iff R g p.a' s).mpr hs.endpoint_adjacent
  have hgc : act R g p.c = p.c := hg
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R p.c).inv_mem hg))
  change (Z R p.c ⊔ Z R p.a').map (MulAut.conj g⁻¹).toMonoidHom = Z R p.c ⊔ Z R p.a' at hmap
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hgc] at hmap
  have hZc : Z R p.c ≤ Q R p.a := by
    apply Z_le_Q_of_dist_lt R p.c (geometry.exists_critical p.c p.before_color)
    rw [geometry.distance_constant p.c p.before_color]
    change _ < geometry.b R
    have hpath := p.before.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm] at hpath
    omega
  have hZg : Z R (act R g p.a') ≤ Q R p.a := by
    have hcol : color R (act R g p.a') = false :=
      (action_preserves_color R g p.a').trans p.end_color
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol)
    rw [geometry.distance_constant _ hcol]
    change _ < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle
      (u := act R g p.a') (v := t) (w := p.a)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hgt)] at htri
    have hpath := ht.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm] at hpath
    omega
  have hjoin : Z R p.c ⊔ Z R p.a' ≤ Q R p.a := hmap ▸ sup_le hZc hZg
  exact (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    (le_sup_right.trans hjoin)

/-- The radius commutator is H_c, using only the initial last-edge identity
and preceding local control after proving actual endpoint movement. -/
theorem radius_eq_H (source : LocalSource L R) (p : Counterexample geometry)
    (hb : 2 < geometry.b R) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) :
    radiusCommutator p.a p.a' = H R p.c := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hct : Adjacent R p.c t := p.before.adjacent (geometry := geometry) ht
  exact (initial.radius_eq_edge t ht).trans
    (moving_edge_eq_at p (by omega) control p.c t p.a' p.before_color hct
      ht.endpoint_adjacent (endpoint_moving source p hb)).2.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Radius
