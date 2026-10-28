module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardNonzero

/-!
# Predecessor slices and full-point radius escape

The predecessor residual moves the last edge of a critical path to the
preceding edge. The transported endpoint is then less than the critical
distance from the start. Since the residual acts on the predecessor Baumann
slice modulo the predecessor seed, that entire endpoint slice lies in the
starting core. If the moving slice has index at most two, the full slice is
exactly the reverse critical kernel, and both critical seed indices are two.
The last edge seed supplies the full central attachment throughout.

This removes the predecessor-slice premise from the backward-shift argument.
Under failure of radius escape, the existing bounds apply to every two-edge
slice. The original residual shift gives a critical path with seed index at
least four, whereas its own predecessor slice now forces index two. The
original full-point replacement supplies the generating edge, so its radius
escapes the predecessor core for both possible cover orders.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed pp.919--920.
The final application proves the radius-escape clause in the full-point
radical-image branch. The other radical images, strict slice selections,
exact-four exclusion, intermediate R4/R6 noncentrality, and both terminal
contradictions remain required for LargeDistanceInput. No natural subgroup
is substituted for the original natural quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem residual_neighbor_transporter
    {c t v : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t) (hcv : Adjacent d.radical c v) :
    ∃ k ∈ Ltilde d.radical c, act d.radical k t = v := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hl) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  have hgen : Ltilde d.radical c ⊔ Q d.radical t = stabilizer d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
    · rw [hg.1] at hcol
      cases hcol
  have hn : Q d.radical t ≤ normalizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer d.radical c :=
      (stabilizer d.radical c).inv_mem (hx.2 _ (adjacent_symm d.radical hct))
    have hh := Ltilde_act d.radical x⁻¹ c
    rw [inv_inv,show act d.radical x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
  have hprod : g ∈ (Q d.radical t : Set (FreeAmalgam d.radical)) *
      (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q d.radical t) (Ltilde d.radical c),hgen]
    exact hg
  obtain ⟨q,hq,k,hk,rfl⟩ := hprod
  refine ⟨k,hk,?_⟩
  have hqt : act d.radical q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

include h in
/-- The last seed's predecessor slice is contained in the starting core.
The predecessor residual moves the last edge two steps back along the
same walk; its action on the slice is trivial modulo the predecessor seed. -/
theorem critical_predecessor_slice_le_core
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Z d.radical a' ⊓ B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _) ≤ Q d.radical a := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let v := p.walk.getVert (p.walk.length-3)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hcv : Adjacent d.radical c v := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hte : Adjacent d.radical t a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct hcv
  have hve : (cosetGraph d.radical).Adj v (act d.radical k a') := by
    rw [←hkt]
    exact (cosetGraph_adj d.radical _ _).mpr ((adjacent_act_iff d.radical k _ _).mpr hte)
  let w := (p.walk.take (p.walk.length-3)).concat hve
  have hw : w.length = p.walk.length-2 := by
    simp only [w,SimpleGraph.Walk.length_concat,SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have heQ : Z d.radical (act d.radical k a') ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ (p.act k).end_color)
    rw [(replacementGeometry h d).distance_constant _ (p.act k).end_color,
      SimpleGraph.dist_comm]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    exact (SimpleGraph.dist_le w).trans_lt (by rw [hw]; change p.walk.length-2 < replacementDistance h d; omega)
  have hcQ : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol)
    rw [(replacementGeometry h d).distance_constant c hcol,SimpleGraph.dist_comm,
      p.dist_start (Nat.sub_le _ _)]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-2 < replacementDistance h d
    omega
  intro x hx
  have hcomm : ⁅k⁻¹,x⁆ ∈ Z d.radical c :=
    ((mem_B_iff d.radical c _ ((replacementGeometry h d).V_le_Q hb c hcol |>.trans (fun _ hx => hx.1)) x).mp hx.2).2
      k⁻¹ ((Ltilde d.radical c).inv_mem hk)
  have hmove : k⁻¹*x*k ∈ Z d.radical (act d.radical k a') := by
    rw [Z_act]
    exact ⟨x,hx.1,by simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
      MulAut.conj_apply,inv_inv]⟩
  have hh := (Q d.radical a).mul_mem ((Q d.radical a).inv_mem (hcQ hcomm)) (heQ hmove)
  simpa only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc,
    inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh

private theorem relIndex_sup_of_normalized {H : Type*} [Group H]
    (A D : Subgroup H) (hn : D ≤ normalizer (A : Set H)) :
    A.relIndex (A ⊔ D) = A.relIndex D := by
  let J := A ⊔ D
  let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hi := relIndex_sup_left (D.subgroupOf J) (A.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

include h in
private theorem critical_predecessor_edges
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    color d.radical (p.walk.getVert (p.walk.length-2)) = false ∧
      Adjacent d.radical (p.walk.getVert (p.walk.length-2)) (p.walk.getVert (p.walk.length-1)) ∧
      Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  refine ⟨?_,?_,?_⟩
  · apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  · have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  · have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)

include s in
/-- A predecessor moving-slice index at most two identifies the full slice
with the reverse critical kernel. Both critical seed indices are exactly two;
the full seed retains the last edge's central attachment. -/
theorem critical_predecessor_slice_eq_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hindex : (B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ≤ 2) :
    Z d.radical a' ⊓ B d.radical (p.walk.getVert (p.walk.length-2))
        ((replacementGeometry h d).Z_normal _) = Z d.radical a' ⊓ Q d.radical a ∧
      (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let Bc := B d.radical c ((replacementGeometry h d).Z_normal _)
  let E := Z d.radical a' ⊓ Bc
  let K := Z d.radical a' ⊓ Q d.radical a
  obtain ⟨hcol,hct,het⟩ := critical_predecessor_edges hb p
  have hE : E ≤ K := le_inf inf_le_left (critical_predecessor_slice_le_core hb p)
  have hZeGc : Z d.radical a' ≤ stabilizer d.radical c := by
    apply Z_le_stabilizer_of_dist_le a' ((replacementGeometry h d).exists_critical _ p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-(p.walk.length-2) ≤ replacementDistance h d
    omega
  have hseedB : Z d.radical t ≤ Bc :=
    (adjacent_Z_le d.radical hcol hct).trans (Escape.EdgeTransfer.Z_le_B hb c hcol)
  have hZeSup : Z d.radical a' ≤ Bc ⊔ U d.radical a' := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color het]
    exact sup_le le_sup_right (hseedB.trans le_sup_left)
  have hBn : stabilizer d.radical c ≤ normalizer (Bc : Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized hb c hcol
  have hUG : U d.radical a' ≤ stabilizer d.radical c := (DistanceEight.U_le_Z d.radical a').trans hZeGc
  have hBG : Bc ≤ stabilizer d.radical c := by
    intro x hx
    exact ((replacementGeometry h d).V_le_Q hb c hcol |>.trans (fun _ hx => hx.1))
      (((mem_B_iff d.radical c _ ((replacementGeometry h d).V_le_Q hb c hcol |>.trans (fun _ hx => hx.1)) x).mp hx).1)
  let := finite_stabilizer d.radical c
  let : Finite (Bc ⊔ U d.radical a' : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le hBG hUG)) (inclusion_injective _)
  let := finite_Z d.radical a'
  have hZi : Bc.relIndex (Z d.radical a') ≤ 2 := by
    calc
      _ ≤ Bc.relIndex (Bc ⊔ U d.radical a') := relIndex_le_of_le_right hZeSup index_ne_zero_of_finite
      _ = Bc.relIndex (U d.radical a') := relIndex_sup_of_normalized _ _ (hUG.trans hBn)
      _ ≤ 2 := hindex
  have hKi : K.relIndex (Z d.radical a') ≤ 2 := by
    have hi := relIndex_le_of_le_left hE (index_ne_zero_of_finite (H := E.subgroupOf (Z d.radical a')))
    exact hi.trans (by simpa only [E,inf_relIndex_left] using hZi)
  have hsmall : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [show (Q d.radical a).relIndex (Z d.radical a') = K.relIndex (Z d.radical a') from
      (inf_relIndex_left _ _).symm]
    omega
  let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color
    (critical_reverse_pair s hc p)
  have hi := small_critical_indices s hc q hsmall
  have hKtwo : K.relIndex (Z d.radical a') = 2 := by
    simpa only [K,inf_relIndex_left] using hi.1
  have hm := relIndex_mul_relIndex E K (Z d.radical a') hE inf_le_left
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Z d.radical a' from inf_le_left))
    (inclusion_injective _)
  have hp : 0 < E.relIndex K := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hEi : E.relIndex (Z d.radical a') ≤ 2 := by simpa only [E,inf_relIndex_left] using hZi
  rw [hKtwo] at hm
  have hEK : E = K := le_antisymm hE (relIndex_eq_one.mp (by omega : E.relIndex K = 1))
  exact ⟨hEK,hi.2,hi.1⟩

include s in
/-- The source backward-shift contradiction with the original generating edge.
Failure of radius escape bounds every predecessor slice by two. The residual
shift produces a critical pair of index at least four, contradicting the
kernel equality on that same shifted path. -/
theorem radius_not_le_predecessor_of_generating_edge
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  have hindices {a₀ a₁ : Vertex d.radical}
      (q : CriticalPath d.radical (replacementGeometry h d) a₀ a₁) :
      Z d.radical a₁ ⊓ B d.radical (q.walk.getVert (q.walk.length-2))
          ((replacementGeometry h d).Z_normal _) = Z d.radical a₁ ⊓ Q d.radical a₀ ∧
        (Q d.radical a₁).relIndex (Z d.radical a₀) = 2 ∧
        (Q d.radical a₀).relIndex (Z d.radical a₁) = 2 := by
    obtain ⟨hcol,hct,het⟩ := critical_predecessor_edges hb q
    exact critical_predecessor_slice_eq_kernel s hc hb q
      (radius_failure_all_slice_indices_le_two s hc hb u hR p hat hgen hbad hcol hct het)
  have hp := hindices p
  have hslice : U d.radical a' ⊓ Q d.radical (alpha d.radical) ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _) :=
    (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical a')).trans (hp.1.ge.trans inf_le_right)
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hcQ : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hbad
  obtain ⟨hcol,hpred,hlast⟩ := critical_predecessor_edges hb p
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hprev : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hpred hprev
  obtain ⟨q,hlarge,hqt,hover,hcomm⟩ := eligible_backward_residual_critical_path
    s hc hb u hR p hat hct hgen hel hcQ hslice k hk hkt
  have hsmall := (hindices q).2.1
  omega

/-- On the original full-point characteristic replacement, the radius
escapes the predecessor core. Both cover orders are allowed, and the action
uses the canonical source quotient. This discharges the radius-escape clause
of MS93 (5.8) in this radical-image branch. -/
theorem full_point_radius_not_le_predecessor_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  exact radius_not_le_predecessor_of_generating_edge s hc hb u hfull'.le p hat hgen

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
