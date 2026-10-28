module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic

/-!
# Endpoint movement before the centralizer selection

A nonmoving endpoint would make the join of its Z-layer and the second
predecessor's Z-layer invariant under that predecessor's stabilizer. Moving
the final edge towards the start puts both layers strictly inside the critical
distance, contradicting reversal of the critical pair. This proves the
movement premise needed to identify R₀ with the predecessor's displacement.

The proof is adapted from `Propagation/Backward/Bound/Radius.lean`, using
only the earlier source and geometry inputs, without importing propagation
or any local-control conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), the paragraph before
(4.3.2)(4), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

private theorem normalizes_sup_of_commutator_le {G : Type*} [Group G]
    (A B K : Subgroup G) (hKA : K ≤ normalizer (A : Set G))
    (hc : ⁅B, K⁆ ≤ A) : K ≤ normalizer (A ⊔ B : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    apply sup_le
    · exact (mem_normalizer_iff_map_conj_eq.mp (hKA hk)).le.trans le_sup_left
    · rintro _ ⟨b, hb, rfl⟩
      have hcb : ⁅k, b⁆ ∈ A := by
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator hk hb)
      have h := (A ⊔ B).mul_mem (mem_sup_left hcb) (mem_sup_right hb)
      simpa [commutatorElement_def, mul_assoc] using h
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

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
    · exact normalizes_sup_of_commutator_le _ _ _
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

/-- The source radius is the displacement at the second predecessor,
after proving the endpoint really belongs to its moving-neighbor set. -/
theorem radius_eq_edge (source : LocalSource L R) (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (initial : InitialFacts p)
    (facts : ContraryLocalFacts geometry) {s : Vertex R} (hs : Before p.a p.a' s 1) :
    radiusCommutator p.a p.a' = edgeDisplacement p.c s :=
  radius_eq_predecessor_edge p initial facts (endpoint_moving source p hb) hs

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
