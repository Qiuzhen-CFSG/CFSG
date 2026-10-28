module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusBounds


/-!
# Radius images in the binary symplectic source

At an M-vertex, the relative index of the two kernels on an edge is the order
of the radical image in S6. The original characteristic replacement puts
that image inside the marked point core, whose order is eight. If the critical
distance is at least four, a radius at distance two lies in the intervening
edge kernel. Its image at the opposite M-vertex therefore also has order at
most eight.

The final applications use the original SourceData and its literal critical
path. They discharge the first image estimate in MS93 (5.2) at distance four,
without assuming radius centrality or an elementary radius quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed p.914.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem edge_kernel_index (a t : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t) :
    (Q R a).relIndex (Q R t) = Nat.card (R.map s.projection) := by
  have hbase : (Q R (alpha R)).relIndex (Q R (beta R)) =
      Nat.card (R.map s.projection) := by
    rw [Q_alpha R s.two_group s.core_le,Q_beta,
      relIndex_map_map_of_injective _ _ (embedM_injective R),
      ←s.projection_kernel,relIndex_ker]
  obtain ⟨g, hg | hg⟩ := edge_transitive R hat (base_adjacent R)
  · have he : (Q R (act R g a)).relIndex (Q R (act R g t)) =
        (Q R a).relIndex (Q R t) := by
      rw [Q_act,Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    rw [hg.1,hg.2] at he
    exact he.symm.trans hbase
  · have ht : color R (beta R) = false := by
      change color R (hVertex R 1) = false
      rw [←hg.1,action_preserves_color,ha]
    cases ht

theorem edge_kernel_index_le_eight (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    (Q R a).relIndex (Q R t) ≤ 8 := by
  rw [edge_kernel_index s a t ha hat]
  have hc := Nat.card_le_card_of_injective (inclusion hR) (inclusion_injective hR)
  have he : Nat.card (pointCore.map (MulAut.conj u).toMonoidHom) = 8 :=
    (card_map_of_injective (MulAut.conj u).injective).trans pointCore_card
  rwa [he] at hc

theorem radius_image_index_le_eight (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 3 < s.geometry.b R) (a e : Vertex R) (ha : color R a = false)
    (hde : (cosetGraph R).dist a e = 2) :
    (Q R e).relIndex (V R a) ≤ 8 := by
  obtain ⟨t,hat,het⟩ := exists_common_neighbor_of_dist_two R a e hde
  have hd : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hV : V R a ≤ Q R t := V_le_Q_of_dist_add_two_lt R ha (by omega)
  have he : color R e = false :=
    (color_eq_of_dist_even R a e (by rw [hde]; decide)).symm.trans ha
  have hidx := edge_kernel_index s e t he het
  have hn : (Q R e).relIndex (Q R t) ≠ 0 := by
    rw [hidx]
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  exact (relIndex_le_of_le_right hV hn).trans
    (edge_kernel_index_le_eight s u hR e t he het)

/-- The order-eight estimate at the actual penultimate M-vertex of a critical
path of length four. -/
theorem critical_radius_image_index_le_eight (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R = 4) {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a') :
    (Q R (p.walk.getVert (p.walk.length-2))).relIndex (V R a) ≤ 8 := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  apply radius_image_index_le_eight s u hR (by omega) a _ p.start_color
  rw [p.dist_start (Nat.sub_le _ _),hl]

end Source
namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

theorem reducedSource_radius_image_index_le_eight (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : 3 < ((originalSource d h).reduce c).geometry.b c.radical)
    (a e : Vertex c.radical) (ha : color c.radical a = false)
    (hde : (cosetGraph c.radical).dist a e = 2) :
    (Q c.radical e).relIndex (V c.radical a) ≤ 8 :=
  Source.radius_image_index_le_eight ((originalSource d h).reduce c)
    d.relabeler.val⁻¹ (reducedSource_radical_image_le d h c) hb a e ha hde

/-- The original characteristic replacement and the literal selected critical
path discharge every premise of the first image estimate in MS93 (5.2). -/
theorem reducedSource_critical_radius_image_index_le_eight (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : ((originalSource d h).reduce c).geometry.b c.radical = 4)
    {a a' : Vertex c.radical}
    (p : CriticalPath c.radical ((originalSource d h).reduce c).geometry a a') :
    (Q c.radical (p.walk.getVert (p.walk.length-2))).relIndex (V c.radical a) ≤ 8 :=
  Source.critical_radius_image_index_le_eight ((originalSource d h).reduce c)
    d.relabeler.val⁻¹ (reducedSource_radical_image_le d h c) hb p

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
