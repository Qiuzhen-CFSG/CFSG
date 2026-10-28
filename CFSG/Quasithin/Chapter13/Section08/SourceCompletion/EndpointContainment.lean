module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Preliminary

/-!
# Containment at the original critical endpoints

The shortest-path bound places each conjugate seed in the opposite endpoint
stabilizer. The first and last edges then bound the whole H-conjugate spans
at the two original endpoints, retaining the chosen transporter. These are
the vertex containments needed for the actual commutator-preimage kernels;
no endpoint-containment or EarlierGeometry record is assumed.

Source: Aschbacher--Smith, F.9.13(2), printed p.322, as used in 13.8.4.
The stronger edge two-core bounds are separate conclusions.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]

theorem f9_conjugate_le_endpoint (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (a b : G0 D.L (D.T:Subgroup G) D.H)
    (hd : (CriticalGeometry.graph D.L (D.T:Subgroup G) D.H).dist
      (a•base _ _ _ false) (b•base _ _ _ true) ≤
        criticalDistance D.L (D.T:Subgroup G) D.H D.V) :
    D.V.conjBy (a:G)≤D.H.conjBy (b:G) := by
  have hf : cosetFamily D.L (D.T:Subgroup G) D.H=ChapterF.Section07.Geometry.family D.LT D.H := by
    funext i
    cases i <;> rfl
  rw [f9_criticalDistance_eq D h] at hd
  change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T:Subgroup G) D.H)).dist
    (a•CosetGeometry.base _ false) (b•CosetGeometry.base _ true)≤h.b at hd
  let a' : (D.LT⊔D.H : Subgroup G) := ⟨a.val,a.property⟩
  let b' : (D.LT⊔D.H : Subgroup G) := ⟨b.val,b.property⟩
  have heDist := congrArg (fun F : Bool → Subgroup (D.LT⊔D.H : Subgroup G) =>
    (Subgroup.CosetGeometry.RankTwo.graph F).dist
      (a' • CosetGeometry.base F false) (b' • CosetGeometry.base F true)) hf
  have hd' : (ChapterF.Section07.Geometry.graph D.LT D.H).dist
      (a' • ChapterF.Section07.Geometry.base D.LT D.H false)
      (b' • ChapterF.Section07.Geometry.base D.LT D.H true) ≤ h.b := by
    rw [←heDist]
    exact hd
  have hc := ChapterF.Section07.CriticalPairs.firstModule_le_stabilizer_at_dist_le
    (ChapterF.Section09.Setup.Hypothesis.family (D:=D)) h.f7Setup h.f7V_ne_bot
    (a:=a'•CosetGeometry.base _ false) (v:=b'•CosetGeometry.base _ true) rfl hd'
  rw [ChapterF.Section07.CriticalPairs.firstModule_translate_base _ _ h.f7Setup.seed_normalized] at hc
  change h.f7Setup.seed.map (MulAut.conj a').toMonoidHom ≤
    MulAction.stabilizer (D.LT⊔D.H : Subgroup G) (b'•CosetGeometry.base _ true) at hc
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,CosetGeometry.stabilizer_base] at hc
  have hc' := map_mono (f:=(D.LT⊔D.H).subtype) hc
  have hm (A:Subgroup (D.LT⊔D.H : Subgroup G)) (g:(D.LT⊔D.H : Subgroup G)) :
      (A.map (MulAut.conj g).toMonoidHom).map (D.LT⊔D.H).subtype=
        (A.map (D.LT⊔D.H).subtype).map (MulAut.conj (g:G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  rw [hm _ a',hm _ b',h.f7Seed_map] at hc'
  have heH : (ChapterF.Section07.Geometry.family D.LT D.H true).map (D.LT⊔D.H).subtype=D.H :=
    map_subgroupOf_eq_of_le le_sup_right
  rw [heH] at hc'
  exact hc'

omit [Finite G] in
private theorem connected (L T H:Subgroup G) : (graph L T H).Connected := by
  change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily L T H)).Connected
  apply Subgroup.CosetGeometry.RankTwo.connected
  have hf : cosetFamily L T H=ChapterF.Section07.Geometry.family (L⊔T) H := by funext i; cases i <;> rfl
  rw [hf]
  exact ChapterF.Section07.Geometry.family_generates _ _

omit [Finite G] in
private theorem second_distance (L T H V:Subgroup G) (c:CriticalPair L T H V)
    (hb:1≤c.path.length) : (graph L T H).dist (base L T H true) c.gamma+1=c.path.length := by
  have he:=SimpleGraph.length_eq_dist_of_subwalk c.distance_eq.symm (c.path.isSubwalk_drop 1)
  rw [SimpleGraph.Walk.drop_length,c.first] at he
  omega

theorem f9_endpoint_spans (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length) :
    Source.VH D.H D.V≤vertexGroup D.L (D.T:Subgroup G) D.H c.gamma ∧ c.Vgamma≤D.H := by
  have hdist:=second_distance D.L (D.T:Subgroup G) D.H D.V c (by omega)
  have hconn:=connected D.L (D.T:Subgroup G) D.H
  have bound (a:D.H) :
      (graph D.L (D.T:Subgroup G) D.H).dist
        ((inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)•base _ _ _ false) c.gamma≤c.path.length := by
    have he:=neighbor (inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)
    rw [inG0_one] at he
    have ht:=hconn.dist_triangle
      (u:=(inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)•base _ _ _ false) (v:=base _ _ _ true) (w:=c.gamma)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr he] at ht
    omega
  constructor
  · rw [c.vertexGroup_gamma]
    change conjugateSpanBy D.V D.H≤D.H.conjBy (c.gb:G)
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro a
    apply f9_conjugate_le_endpoint D h ((inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)) c.gb
    rw [c.gb_one,←c.length_eq]
    exact bound a
  · change (conjugateSpanBy D.V D.H).map (MulAut.conj (c.gb:G)).toMonoidHom≤D.H
    rw [conjugateSpanBy_eq_iSup_conj,Subgroup.map_iSup]
    apply iSup_le
    intro a
    have he:=neighbor (c.gb*inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)
    simp only [mul_smul,inG0_one,c.gb_one] at he
    have ht:=hconn.dist_triangle
      (u:=(c.gb*(inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a))•base _ _ _ false) (v:=c.gamma) (w:=base _ _ _ true)
    simp only [mul_smul] at ht
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr he,SimpleGraph.dist_comm (u:=c.gamma)] at ht
    have hd : (graph D.L (D.T:Subgroup G) D.H).dist
        ((c.gb*(inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a))•base _ _ _ false) ((1 : G0 D.L (D.T:Subgroup G) D.H)•base _ _ _ true)≤criticalDistance D.L (D.T:Subgroup G) D.H D.V := by
      rw [one_smul,←c.length_eq]
      simp only [mul_smul]
      omega
    have hm:=f9_conjugate_le_endpoint D h (c.gb*(inG0 (L:=D.L) (T:=(D.T:Subgroup G)) a)) 1 hd
    rw [Subgroup.coe_mul,Subgroup.coe_one,conjBy_one,conjBy_mul] at hm
    change (D.V.conjBy (a:G)).conjBy (c.gb:G) ≤ D.H at hm
    exact hm
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
