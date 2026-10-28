module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels

/-!
# The actual two-core bounds at both critical edges

The F.7 neighbor-join theorem applies to the original shortest path.
Transport of the literal second-vertex module identifies its ambient image
with VH, and the same endpoint conjugator identifies the other image with
V-gamma. The two internal geodesic segment lengths then place these spans
in the opposite edge two-cores. No core-placement premise is used.

Source: Aschbacher--Smith, F.7.11(5--6), F.9.13(2), printed pp.314,322.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]

theorem f9_span_le_edge_core (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (a:G0 D.L (D.T:Subgroup G) D.H) (v w:Vertex D.L (D.T:Subgroup G) D.H)
    (hd:(graph D.L (D.T:Subgroup G) D.H).dist (a•base _ _ _ true) v+2=
      criticalDistance D.L (D.T:Subgroup G) D.H D.V)
    (hadj:(graph D.L (D.T:Subgroup G) D.H).Adj v w) :
    (Source.VH D.H D.V).map (MulAut.conj (a:G)).toMonoidHom≤
      (edgeGroup D.L (D.T:Subgroup G) D.H v w).pCoreIn 2 := by
  have hf:cosetFamily D.L (D.T:Subgroup G) D.H=ChapterF.Section07.Geometry.family D.LT D.H := by
    funext i
    cases i <;> rfl
  let F:=ChapterF.Section07.Geometry.family D.LT D.H
  have hm : ∀ (s v w:Subgroup.CosetGeometry.Vertex F), s.type=true →
      (Subgroup.CosetGeometry.RankTwo.graph F).dist s v+2=h.b →
      (Subgroup.CosetGeometry.RankTwo.graph F).Adj v w →
      (ChapterF.Section07.CriticalPairs.vertexModule F (D.V.subgroupOf (D.LT⊔D.H)) s).map (D.LT⊔D.H).subtype≤
      ((Subgroup.CosetGeometry.RankTwo.stabilizer F v).map (D.LT⊔D.H).subtype⊓
        (Subgroup.CosetGeometry.RankTwo.stabilizer F w).map (D.LT⊔D.H).subtype).pCoreIn 2 := by
    intro s v w hs hd he
    have hc:=ChapterF.Section07.CriticalPairs.geodesic_edge_core F h.f7Setup h.f7V_ne_bot hs hd he
    have hh:=map_mono (f:=(D.LT⊔D.H).subtype) hc
    rw [h.f7Seed_eq,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (D.LT⊔D.H).subtype_injective,Subgroup.map_inf _ _ _ (D.LT⊔D.H).subtype_injective] at hh
    exact hh
  have hb : (ChapterF.Section07.CriticalPairs.vertexModule F (D.V.subgroupOf (D.LT⊔D.H))
      (Subgroup.CosetGeometry.base F true)).map (D.LT⊔D.H).subtype=Source.VH D.H D.V := by
    rw [←h.f7Seed_eq,ChapterF.Section07.CriticalPairs.second_base_module_eq_conjugate_join _ _ h.f7Setup.seed_normalized,
      ←conjugateSpanBy_eq_iSup_conj,map_conjugateSpanBy,h.f7Seed_map]
    rw [show (F true).map (D.LT⊔D.H).subtype=D.H from map_subgroupOf_eq_of_le le_sup_right]
    rfl
  have hnorm : F false≤normalizer (D.V.subgroupOf (D.LT⊔D.H):Set (D.LT⊔D.H : Subgroup G)) := by
    rw [←h.f7Seed_eq]
    exact h.f7Setup.seed_normalized
  dsimp only [F] at hm hb hnorm
  rw [←hf] at hm hb hnorm
  rw [f9_criticalDistance_eq D h] at hd
  have hc:=hm (a•base _ _ _ true) v w rfl hd hadj
  let a' : (D.LT⊔D.H : Subgroup G) := ⟨a.val,a.property⟩
  have htr:=ChapterF.Section07.CriticalPairs.vertexModule_translate _ _ hnorm a' (CosetGeometry.base (cosetFamily D.L (D.T:Subgroup G) D.H) true)
  change ChapterF.Section07.CriticalPairs.vertexModule (cosetFamily D.L (D.T:Subgroup G) D.H) (D.V.subgroupOf (D.LT⊔D.H)) (a•base _ _ _ true)=_ at htr
  have htrmap:=congrArg (fun A:Subgroup (D.LT⊔D.H : Subgroup G)=>A.map (D.LT⊔D.H).subtype) htr
  have hc':=htrmap.ge.trans hc
  have hmap (A:Subgroup (D.LT⊔D.H : Subgroup G)) :
      (A.map (MulAut.conj a').toMonoidHom).map (D.LT⊔D.H).subtype=
      (A.map (D.LT⊔D.H).subtype).map (MulAut.conj (a:G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  exact (congrArg (fun A:Subgroup G=>A.map (MulAut.conj (a:G)).toMonoidHom) hb).ge.trans
    ((hmap _).ge.trans hc')

theorem f9_endpoint_edge_cores (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length) :
    Source.VH D.H D.V≤(edgeGroup D.L (D.T:Subgroup G) D.H c.previous c.gamma).pCoreIn 2 ∧
    c.Vgamma≤(edgeGroup D.L (D.T:Subgroup G) D.H (base _ _ _ true) c.second).pCoreIn 2 := by
  have hpen:=c.path.adj_getVert_succ (i:=c.path.length-1) (by omega)
  rw [show c.path.length-1+1=c.path.length by omega,c.path.getVert_length] at hpen
  have hseg:=SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk c.distance_eq.symm (c.path.isSubwalk_take (c.path.length-1)))
    ((c.path.take (c.path.length-1)).isSubwalk_drop 1)
  have hstart:(c.path.take (c.path.length-1)).getVert 1=base _ _ _ true := by
    rw [SimpleGraph.Walk.take_getVert,min_eq_right (by omega),c.first]
  rw [SimpleGraph.Walk.drop_length,SimpleGraph.Walk.take_length,min_eq_left (Nat.sub_le _ _),hstart] at hseg
  have htwo:=c.path.adj_getVert_succ (i:=1) (by omega)
  rw [c.first] at htwo
  have hend:=SimpleGraph.length_eq_dist_of_subwalk c.distance_eq.symm (c.path.isSubwalk_drop 2)
  rw [SimpleGraph.Walk.drop_length,SimpleGraph.dist_comm] at hend
  constructor
  · have hh:=f9_span_le_edge_core D h 1 c.previous c.gamma (by
      rw [one_smul,←c.length_eq]
      change (graph _ _ _).dist _ (c.path.getVert (c.path.length-1))+2=c.path.length
      omega) hpen
    have hmap:(MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G := by ext x; simp
    simpa only [Subgroup.coe_one,hmap,Subgroup.map_id] using hh
  · have hh:=f9_span_le_edge_core D h c.gb c.second (base _ _ _ true) (by
      rw [c.gb_one,←c.length_eq]
      change (graph _ _ _).dist c.gamma (c.path.getVert 2)+2=c.path.length
      omega) htwo.symm
    change c.Vgamma≤(vertexGroup _ _ _ c.second⊓vertexGroup _ _ _ (base _ _ _ true)).pCoreIn 2 at hh
    rwa [inf_comm] at hh

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
