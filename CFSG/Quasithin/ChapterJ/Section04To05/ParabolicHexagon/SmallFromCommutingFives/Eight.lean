module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SmallFromCommutingFives.Neighbors
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath

/-!
# Exact distance eight from the commuting-five configuration

A fourth-vertex fixer moves the base by at most eight. The central-label
product of order5 excludes distances at most four and distance six using
the genuine short-path label calculations; bipartite parity forces eight.
The base rotation moves the first edge of a shortest path while fixing
both endpoints, producing the two distinct geodesics required for Small.
No eight-path metric transfer or completion recognition is used.

Source: Aschbacher–Smith J.4.10, printed p.445, using F.4.6.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
open Subgroup Subgroup.CosetGeometry.RankTwo
open ChapterF.SourceCompletion.BinaryRee FiveHexagon.PathTransport FiveHexagon.MarkedInverter
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
variable {K:Type*} [Group K] (q:Completion K)

 theorem distance_eight_of_fourth_fixer (b:K)
    (hb:b•(completionFourthWord q•basePoint q)=completionFourthWord q•basePoint q)
    (ho:orderOf (centralRoot q*(b*centralRoot q*b⁻¹))=5) :
    q.graph.dist (basePoint q) (b•basePoint q)=8 := by
  let x:=basePoint q
  let w:=completionFourthWord q•basePoint q
  have h4:q.graph.dist x w=4:=four_point_distance q
  have h4':q.graph.dist w (b•x)=4:=by
    calc
      _=q.graph.dist (b•w) (b•x):=by rw [hb]
      _=q.graph.dist w x:=q.graphAction.dist_smul b w x
      _=4:=q.graph.dist_comm.trans h4
  have hub:q.graph.dist x (b•x)≤8:=by
    have hh:=q.connected.dist_triangle (u:=x) (v:=w) (w:=b•x)
    rw [h4,h4'] at hh
    exact hh
  have hnot:¬q.graph.dist x (b•x)≤4:=by
    intro hd
    have hc:=short_point_labels_commute q b hd
    have hr:orderOf (centralRoot q)=2:=by
      rw [centralRoot,modelZ_middle]
      exact completion_root_order q
    have h2:(centralRoot q)^2=1:=by rw [←hr];exact pow_orderOf_eq_one _
    have hb2:(b*centralRoot q*b⁻¹)^2=1:=by
      calc
        _=b*(centralRoot q)^2*b⁻¹:=by simp only [pow_two];group
        _=1:=by rw [h2];simp
    have hh:(centralRoot q*(b*centralRoot q*b⁻¹))^2=1:=by
      rw [hc.mul_pow,h2,hb2,mul_one]
    have hd5:=orderOf_dvd_of_pow_eq_one hh
    rw [ho] at hd5
    norm_num at hd5
  have hn6:q.graph.dist x (b•x)≠6:=by
    intro h6
    have hh:=six_point_labels_product_order q b h6
    rw [ho] at hh
    contradiction
  have heven:Even (q.graph.dist x (b•x)):=(even_dist_iff q.family q.generated _ _).mpr rfl
  obtain ⟨n,hn⟩:=heven
  change q.graph.dist x (b•x)=8
  omega

 theorem small_of_fourth_fixer (b:K)
    (hb:b•(completionFourthWord q•basePoint q)=completionFourthWord q•basePoint q)
    (ho:orderOf (centralRoot q*(b*centralRoot q*b⁻¹))=5)
    (hc:Commute (q.left modelRotation) b) : q.Small := by
  have hd:=distance_eight_of_fourth_fixer q b hb ho
  obtain ⟨p,hp⟩:=q.connected.exists_walk_length_eq_dist (basePoint q) (b•basePoint q)
  rw [hd] at hp
  have hrx:q.left modelRotation•basePoint q=basePoint q:=by
    change q.left modelRotation∈MulAction.stabilizer K (base q.family false)
    rw [Subgroup.CosetGeometry.stabilizer_base]
    exact ⟨modelRotation,rfl⟩
  have hry:q.left modelRotation•(b•basePoint q)=b•basePoint q:=by
    rw [←mul_smul,hc.eq,mul_smul,hrx]
  apply q.small_of_moves_walk (basePoint q) (b•basePoint q) hd p hp
    (q.left modelRotation) hrx hry 1
  apply rotation_moves_neighbor q
  simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using p.adj_getVert_succ (i:=0) (by omega)
end CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
