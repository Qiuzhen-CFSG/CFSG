module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicResidualShift

/-!
# Predecessor slices on the original cubic graph

A residual element moves the last edge of a critical walk to the preceding
edge. The shifted endpoint is strictly closer to the original start, so
its seed lies in the starting two-core. On the predecessor Baumann slice,
the residual acts trivially modulo the predecessor seed, which is also
in that two-core. Thus the entire predecessor slice lies in the starting
two-core, without assuming midpoint conjugacy or a small critical image.

If the moving-cover slice has index at most two, the full seed slice has
the same bound: the last edge seed belongs to the Baumann subgroup.
Criticality then identifies this slice with the full reverse critical
kernel. Both critical images have order two. Contrapositively, a large
critical image forces both reciprocal slices to have index greater than
two. The full cubic kernel and both covers of orders sixteen and thirty-two
are retained.

CubicRadiusEscape applies this calculation to the original whole-core
and literal C.1.32 consumers. The strict-slice conclusion here concerns
large critical images; the remaining small-image branch of MS93 (5.9)
and the terminal exclusions are still required.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed pp.919--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h in
private theorem residual_neighbor_transporter
    {c t v : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t) (hcv : Adjacent Rg c v) :
    ∃ k ∈ Ltilde Rg c, act Rg k t = v := by
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hcol
    · exact hct
  have hn : Q Rg t ≤ normalizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer Rg c :=
      (stabilizer Rg c).inv_mem (hx.2 _ (adjacent_symm Rg hct))
    have hh := Ltilde_act Rg x⁻¹ c
    rw [inv_inv,show act Rg x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg c hct hcv
  have hprod : g ∈ (Q Rg t : Set (FreeAmalgam Rg)) *
      (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q Rg t) (Ltilde Rg c),hgen]
    exact hg
  obtain ⟨q,hq,k,hkm,rfl⟩ := hprod
  refine ⟨k,hkm,?_⟩
  have hqt : act Rg q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

private theorem relIndex_sup_of_normalized {G : Type*} [Group G]
    (B A : Subgroup G) (hn : A≤normalizer (B:Set G)) :
    B.relIndex (B⊔A)=B.relIndex A := by
  let J := B⊔A
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hi := relIndex_sup_left (A.subgroupOf J) (B.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

include h in
/-- Moving the last edge toward the start places the full predecessor
Baumann slice inside the starting two-core. -/
theorem critical_predecessor_slice_le_start_core
    (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    Z Rg a' ⊓ B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _) ≤ Q Rg a := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let v := p.walk.getVert (p.walk.length-3)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcv : Adjacent Rg c v := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hta : Adjacent Rg t a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter (h := h) hc hct hcv
  have hend : (cosetGraph Rg).Adj v (act Rg k a') := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr ((adjacent_act_iff Rg k _ _).mpr hta)
  have hd : (cosetGraph Rg).dist a (act Rg k a') < sourceDistance h := by
    have hh := SimpleGraph.dist_le ((p.walk.take (p.walk.length-3)).concat hend)
    rw [SimpleGraph.Walk.length_concat,SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] at hh
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hcol : color Rg (act Rg k a') = false := by
    exact (action_preserves_color Rg k a').trans p.end_color
  have hshift : Z Rg (act Rg k a') ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hcol)
    rw [(sourceGeometry h).distance_constant _ hcol,SimpleGraph.dist_comm]
    exact hd
  have hZc : Z Rg c ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,SimpleGraph.dist_comm,
      p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-2 < sourceDistance h
    omega
  intro x hx
  have hconj : k⁻¹*x*k ∈ Q Rg a := by
    apply hshift
    rw [Z_act]
    exact ⟨x,hx.1,by simp⟩
  have hcomm : ⁅k⁻¹,x⁆ ∈ Q Rg a := by
    apply hZc
    exact ((mem_B_iff Rg c _ (((sourceGeometry h).V_le_Q hb c hc).trans
      (fun _ hx => hx.1)) x).mp hx.2).2 k⁻¹ ((Ltilde Rg c).inv_mem hkm)
  have heq : x = ⁅k⁻¹,x⁆⁻¹*(k⁻¹*x*k) := by
    simp [commutatorElement_def,mul_assoc]
  rw [heq]
  exact (Q Rg a).mul_mem ((Q Rg a).inv_mem hcomm) hconj

include h e hz hk in
/-- A predecessor slice of index at most two is exactly the full reverse
critical kernel, and both critical images have order two. -/
theorem critical_predecessor_small_slice
    (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2) :
    Z Rg a' ⊓ B Rg (p.walk.getVert (p.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg a' ⊓ Q Rg a ∧
      (Q Rg a).relIndex (Z Rg a') = 2 ∧
      (Q Rg a').relIndex (Z Rg a) = 2 := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let Bc := B Rg c ((sourceGeometry h).Z_normal _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hseed : Z Rg a' = U Rg a' ⊔ Z Rg t := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg a' t).mp hat
    · rw [hg.1,hg.2]
      have he := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
      rw [graph_U_map h e hz] at he
      have hm := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
        A.map (MulAut.conj g⁻¹).toMonoidHom) he
      rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at hm
      simpa [alpha,beta] using hm
    · have hh := p.end_color
      rw [hg.1] at hh
      cases hh
  have hseedB : Z Rg t ≤ Bc :=
    (adjacent_Z_le Rg hc hct).trans (Escape.EdgeTransfer.Z_le_B hb c hc)
  have hZeSup : Z Rg a' ≤ Bc ⊔ U Rg a' := by
    rw [hseed]
    exact sup_le le_sup_right (hseedB.trans le_sup_left)
  have hZeGc : Z Rg a' ≤ stabilizer Rg c := by
    apply Z_le_stabilizer_of_dist_le a' ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-(p.walk.length-2) ≤ sourceDistance h
    omega
  have hUG := (DistanceEight.U_le_Z Rg a').trans hZeGc
  have hVG := ((sourceGeometry h).V_le_Q hb c hc).trans (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hBG : Bc ≤ stabilizer Rg c := by
    intro x hx
    exact hVG (((mem_B_iff Rg c _ hVG x).mp hx).1)
  let := finite_stabilizer Rg c
  let : Finite (Bc ⊔ U Rg a' : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (sup_le hBG hUG)) (inclusion_injective _)
  let := finite_Z Rg a'
  have hZi : Bc.relIndex (Z Rg a') ≤ 2 := by
    calc
      _ ≤ Bc.relIndex (Bc ⊔ U Rg a') := relIndex_le_of_le_right hZeSup index_ne_zero_of_finite
      _ = Bc.relIndex (U Rg a') := relIndex_sup_of_normalized _ _
        (hUG.trans (Escape.Propagation.Rigidity.B_normalized hb c hc))
      _ ≤ 2 := hindex
  let E := Z Rg a' ⊓ Bc
  let F := Z Rg a' ⊓ Q Rg a
  have hEF : E ≤ F := le_inf inf_le_left (critical_predecessor_slice_le_start_core h hb p)
  have hreverse := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]
      exact sourceDistance_pos h) a' p.end_color p.critical
  have hF : 1 < F.relIndex (Z Rg a') := by
    have hp : 0 < F.relIndex (Z Rg a') := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : F.relIndex (Z Rg a') ≠ 1 :=
      fun he => hreverse.2 ((relIndex_eq_one.mp he).trans inf_le_right)
    omega
  have hm := relIndex_mul_relIndex E F (Z Rg a') hEF inf_le_left
  have hE : E.relIndex (Z Rg a') ≤ 2 := by simpa only [E,inf_relIndex_left] using hZi
  let : Finite F := Finite.of_injective (inclusion (show F ≤ Z Rg a' from inf_le_left)) (inclusion_injective _)
  have hp : 0 < E.relIndex F := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hEF1 : E.relIndex F = 1 := by nlinarith
  have heq : E = F := le_antisymm hEF (relIndex_eq_one.mp hEF1)
  have hsmall : (Q Rg a).relIndex (Z Rg a') < 4 := by
    have hh : F.relIndex (Z Rg a') ≤ 2 := by nlinarith
    rw [show F = Z Rg a' ⊓ Q Rg a from rfl,inf_relIndex_left] at hh
    omega
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color hreverse
  have hi := small_critical_indices h e hz hk q hsmall
  exact ⟨heq,hi.1,hi.2⟩

include h e hz hk in
/-- A large critical image forces a strict predecessor slice. This
conclusion holds independently of the radical's point-core image. -/
theorem large_critical_predecessor_slice_gt_two
    (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    2 < (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') := by
  by_contra! hsmall
  have hi := (critical_predecessor_small_slice h e hz hk hb p hsmall).2.2
  omega

include h e hz hk in
/-- Both reciprocal slices on a large-image critical walk are strict.
The start slice uses the literal reverse walk, preserving its second vertex. -/
theorem large_critical_slices_gt_two
    (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    2 < (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ∧
    2 < (B Rg (p.walk.getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
  refine ⟨large_critical_predecessor_slice_gt_two h e hz hk hb p hlarge,?_⟩
  let q : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant _ p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hqvert : q.walk.getVert (q.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    congr 1
    omega
  by_contra! hs
  have hs' : (B Rg (q.walk.getVert (q.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) ≤ 2 := by
    rwa [hqvert]
  have hi := (critical_predecessor_small_slice h e hz hk hb q hs').2.1
  omega


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
