module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongImages

/-!
# Paired backward chains on the original cubic plane graph

Both selected kernel generators and both endpoint seeds are retained while
orienting the backward path over the original path. Transport and repeated
selection retain the original graph, the actual component element, and every
overlap vertex. No power assertion modulo the two-core is imposed on this
component element: the original projection kernel retains its cubic layer.

Source: Meierfrankenfeld--Stellmacher (1993), (5.6)--(5.11), pp.917--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : Nat.card (center (L ⧸ pCore 2 L)) = 3}
  {hk : layerKernel L R = extensionKernel h}
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- The simultaneous two-kernel and two-endpoint choice, oriented over the
original critical path. This has no single-endpoint generation field. -/
structure PlanePairedBackwardShift {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') where
  start : Vertex Rg
  edge : Vertex Rg
  transporter : FreeAmalgam Rg
  transporter_mem : transporter ∈ stabilizer Rg a
  first_eq : act Rg transporter (p.walk.getVert 1) = edge
  start_eq : act Rg transporter (p.walk.getVert 2) = start
  adjacent_start : Adjacent Rg a edge
  adjacent_shift : Adjacent Rg start edge
  cubic : FreeAmalgam Rg
  cubic_mem : cubic ∈ Ltilde Rg a
  kernel_generation : Q Rg edge ⊔
    (Q Rg edge).map (MulAut.conj cubic).toMonoidHom = stabilizer Rg a
  endpoint_generation : Q Rg edge ⊔ Z Rg a' ⊔
    Z Rg (act Rg cubic a') = stabilizer Rg a
  path : CriticalPath Rg (sourceGeometry h) start
    (p.walk.getVert (p.walk.length-2))
  first : path.walk.getVert 1 = edge
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert (i+2) = p.walk.getVert i

private theorem map_conj_conj {F : Type*} [Group F] (A : Subgroup F) (x y : F) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map
        (MulAut.conj (y*x*y⁻¹)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro z
  change y*(x*z*x⁻¹)*y⁻¹=(y*x*y⁻¹)*(y*z*y⁻¹)*(y*x*y⁻¹)⁻¹
  group

/-- Transport preserves the same paired generators, conjugated by the
literal graph action, together with the parent walk and every overlap. -/
theorem PlanePairedBackwardShift.conjugate {a a' : Vertex Rg}
    {p : CriticalPath Rg (sourceGeometry h) a a'}
    (q : PlanePairedBackwardShift (h := h) p) (j : FreeAmalgam Rg) :
    Nonempty (PlanePairedBackwardShift (h := h) (p.act j)) := by
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hact (x : FreeAmalgam Rg) (v : Vertex Rg) :
      act Rg (f x) (act Rg j v) = act Rg j (act Rg x v) := by
    simp only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,←act_mul]
    congr 1
    group
  have hstab : f q.transporter ∈ stabilizer Rg (act Rg j a) := by
    rw [stabilizer_act]
    exact mem_map_of_mem _ q.transporter_mem
  have hcubic : f q.cubic ∈ Ltilde Rg (act Rg j a) := by
    rw [Ltilde_act]
    exact mem_map_of_mem _ q.cubic_mem
  have hex : ∃ w : CriticalPath Rg (sourceGeometry h)
      (act Rg j q.start) ((p.act j).walk.getVert ((p.act j).walk.length-2)),
      w.walk.getVert 1=act Rg j q.edge ∧
      ∀ i ≤ (p.act j).walk.length-2, w.walk.getVert (i+2)=(p.act j).walk.getVert i := by
    have hend : (p.act j).walk.getVert ((p.act j).walk.length-2) =
        act Rg j (p.walk.getVert (p.walk.length-2)) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert]
    rw [hend]
    refine ⟨q.path.act j,?_,?_⟩
    · simp only [CriticalPath.act,actWalk_getVert,q.first]
    · intro i hi
      have hi0 : i ≤ p.walk.length-2 := by
        simpa only [CriticalPath.act,actWalk_length] using hi
      simp only [CriticalPath.act,actWalk_getVert,q.overlap i hi0]
  obtain ⟨w,hw1,hwo⟩ := hex
  refine ⟨⟨act Rg j q.start,act Rg j q.edge,f q.transporter,hstab,
    ?_,?_,(adjacent_act_iff Rg j _ _).mpr q.adjacent_start,
    (adjacent_act_iff Rg j _ _).mpr q.adjacent_shift,
    f q.cubic,hcubic,?_,?_,w,hw1,hwo⟩⟩
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act Rg j) q.first_eq
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act Rg j) q.start_eq
  · have hh := congrArg (Subgroup.map f) q.kernel_generation
    rw [Subgroup.map_sup,map_conj_conj] at hh
    simpa only [Q_act,stabilizer_act,f,inv_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply] using hh
  · have hh := congrArg (Subgroup.map f) q.endpoint_generation
    simpa only [Subgroup.map_sup,hact,Q_act,Z_act,stabilizer_act,f] using hh

variable (h e hz hk)

include h e hz hk in
private theorem paired_backward_shift_base
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    Nonempty (PlanePairedBackwardShift (h := h) p) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall := plane_long_critical_image_small h e hz hk hb u hR p
  obtain ⟨t,hat,r,hr,q,hq,_,hgen,hpair,_,_,g,hg,hgt,_,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p hsmall hdelta
      (plane_long_forward_slice_strict h e hz hk hb u hR p)
  let x := (embedM Rg r)⁻¹
  change ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) at hq
  have hx : x ∈ Ltilde Rg (alpha Rg) := by
    rw [graph_component h]
    exact inv_mem (mem_map_of_mem _ hr)
  have hxG : x ∈ stabilizer Rg (alpha Rg) := Ltilde_le_stabilizer _ hx
  have hfix : act Rg x (alpha Rg) = alpha Rg := hxG
  have hatx : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←hfix]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  change Q Rg t ⊔ Z Rg a' ⊔ Z Rg (act Rg x a') = stabilizer Rg (alpha Rg) at hgen
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hatx] at hpair
  have hback : (Q Rg (act Rg x t)).map (MulAut.conj x).toMonoidHom = Q Rg t := by
    have hh := Q_act Rg x⁻¹ (act Rg x t)
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using hh.symm
  have hG : (stabilizer Rg (alpha Rg)).map (MulAut.conj x).toMonoidHom =
      stabilizer Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer hxG)
  have hpair0 := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hpair
  rw [Subgroup.map_sup,hback,hG,
    sup_comm ((Q Rg t).map (MulAut.conj x).toMonoidHom) (Q Rg t)] at hpair0
  have hct : Adjacent Rg (act Rg g (p.walk.getVert 2)) t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hpair0,hgen,v,hvt,hover⟩⟩
  · let y := g*x⁻¹
    have hxG : x ∈ stabilizer Rg (alpha Rg) := Ltilde_le_stabilizer _ hx
    have hy : y ∈ stabilizer Rg (alpha Rg) := mul_mem hg (inv_mem hxG)
    have hfix : act Rg x⁻¹ (alpha Rg) = alpha Rg := inv_mem hxG
    have hat' : Adjacent Rg (alpha Rg) (act Rg x⁻¹ t) := by
      rw [←hfix]
      exact (adjacent_act_iff Rg x⁻¹ _ _).mpr hat
    have hyt : act Rg y (p.walk.getVert 1) = act Rg x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act Rg x⁻¹ (act Rg g (p.walk.getVert 2)) =
        act Rg y (p.walk.getVert 2) := (act_mul Rg g x⁻¹ _).symm
    have hct' : Adjacent Rg (act Rg y (p.walk.getVert 2))
        (act Rg x⁻¹ t) := by
      rw [←hstart]
      exact (adjacent_act_iff Rg x⁻¹ _ _).mpr hct
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act Rg x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath Rg (sourceGeometry h)
        (act Rg y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 1=act Rg x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      have hex : ∃ w : CriticalPath Rg (sourceGeometry h)
          (act Rg x⁻¹ (act Rg g (p.walk.getVert 2)))
          (act Rg x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act Rg x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          simp only [CriticalPath.act,actWalk_getVert,hover i (hlen.symm ▸ hi),hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
    obtain ⟨w,hw1,hwo⟩ := hex
    refine ⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,w,hw1,hwo⟩⟩
    · rw [Q_act,inv_inv,map_map]
      have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam Rg) := by
        apply MonoidHom.ext
        intro z
        change x⁻¹*(x*z*x⁻¹)*(x⁻¹)⁻¹=z
        group
      rw [he,map_id]
      exact (sup_comm _ _).trans hpair0
    · have hQt : (Q Rg t).map (MulAut.conj x).toMonoidHom =
          Q Rg (act Rg x⁻¹ t) := by rw [Q_act,inv_inv]
      have hZa (z : Vertex Rg) : (Z Rg z).map (MulAut.conj x).toMonoidHom =
          Z Rg (act Rg x⁻¹ z) := by rw [Z_act,inv_inv]
      have hGa : (stabilizer Rg (alpha Rg)).map (MulAut.conj x).toMonoidHom =
          stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen
      simp only [Subgroup.map_sup,hQt,hZa,hGa,←act_mul,mul_inv_cancel,act_one] at hh
      calc
        _ = Q Rg (act Rg x⁻¹ t) ⊔ Z Rg (act Rg x⁻¹ a') ⊔
          Z Rg a' := by ac_rfl
        _ = _ := hh

private theorem paired_backward_shift_of_vertices
    {a a' c c' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : CriticalPath Rg (sourceGeometry h) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (PlanePairedBackwardShift (h := h) q)) :
    Nonempty (PlanePairedBackwardShift (h := h) p) := by
  subst c
  subst c'
  obtain ⟨r⟩ := hr
  have hl : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hex : ∃ w : CriticalPath Rg (sourceGeometry h) r.start
      (q.walk.getVert (q.walk.length-2)),
      w.walk.getVert 1=r.edge ∧
      ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
    refine ⟨r.path,r.first,?_⟩
    intro i hi
    rw [r.overlap i (by omega),hv]
  rw [hl,hv] at hex
  obtain ⟨w,hw1,hwo⟩ := hex
  exact ⟨⟨r.start,r.edge,r.transporter,r.transporter_mem,
    by simpa only [hv] using r.first_eq,by simpa only [hv] using r.start_eq,
    r.adjacent_start,r.adjacent_shift,r.cubic,r.cubic_mem,
    r.kernel_generation,r.endpoint_generation,w,hw1,hwo⟩⟩

include h e hz hk in
/-- Repeated source selection on the original cubic plane graph retains both
generating pairs at every vertex, with no critical-image or strict-slice premise. -/
theorem plane_long_paired_backward_shift
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    Nonempty (PlanePairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg j⁻¹ a = alpha Rg := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := paired_backward_shift_base h e hz hk
    hb u hR (a' := act Rg j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex Rg) : act Rg j (act Rg j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact paired_backward_shift_of_vertices h p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)

include h e hz hk in
/-- The actual shifted critical line has order two, lies in the selected
edge seed and the old starting seed, and centralizes the full old endpoint
radius. Its noncentrality remains at its own starting stabilizer. -/
theorem plane_long_paired_shift_commutator
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : PlanePairedBackwardShift (h := h) p) :
    let H := ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆
    Nat.card H = 2 ∧ H ≤ Z Rg q.edge ∧ H ≤ Z Rg a ∧
      H ≤ centralizer (Q Rg q.edge : Set (FreeAmalgam Rg)) ∧
      H ≤ centralizer (V Rg a' : Set (FreeAmalgam Rg)) ∧
      ¬ H ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆
  have hHt : H ≤ Z Rg q.edge := by
    simpa only [q.first] using plane_critical_commutator_le_first_seed h e hz hk u hR q.path
  have hHe : H ≤ Z Rg (p.walk.getVert (p.walk.length-2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le).trans
        (Z_normalized Rg _))
  have ht : color Rg q.edge=true := by
    have hh := adjacent_color_ne Rg q.adjacent_start
    rw [p.start_color] at hh
    cases he : color Rg q.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q Rg q.edge : Set (FreeAmalgam Rg)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hVQ : V Rg a' ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) p.end_color
    change (cosetGraph Rg).dist a' (p.walk.getVert (p.walk.length-2)) + 2 <
      sourceDistance h
    rw [SimpleGraph.dist_comm,p.dist_end]
    have hl : p.walk.length=sourceDistance h := p.length_eq_b
    omega
  have hHV : H ≤ centralizer (V Rg a' : Set (FreeAmalgam Rg)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ q.path.end_color))).trans (centralizer_le hVQ)
  exact ⟨(plane_long_critical_indices_two h e hz hk hb u hR q.path).2.2,hHt,hHt.trans (adjacent_Z_le Rg p.start_color q.adjacent_start),
    hHQ,hHV,critical_commutator_not_central h e hz hk q.path⟩

include h e hz hk in
/-- Three simultaneous source choices over one coherent chain. The literal
R₄ and R₆ both centralize the full radius at the R₄ endpoint. Both generating
pairs and the cubic lifts are retained by each shift, including when an
inverse orientation was selected. No centrality at an intermediate
stabilizer is inferred from these radius bounds. -/
theorem plane_long_three_paired_shifts
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ q : PlanePairedBackwardShift (h := h) p,
      ∃ r : PlanePairedBackwardShift (h := h) q.path,
        ∃ t : PlanePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z Rg r.start,Z Rg z₄⁆
          let R₆ := ⁅Z Rg t.start,Z Rg z₆⁆
          Nat.card R₄ = 2 ∧ Nat.card R₆ = 2 ∧
          R₄ ≤ Z Rg r.edge ⊓ Z Rg q.start ∧
          R₆ ≤ Z Rg t.edge ⊓ Z Rg r.start ∧
          R₄ ⊔ R₆ ≤ centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) ∧
          R₄ ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) ∧
          ¬ R₄ ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) ∧
          ¬ R₆ ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
  obtain ⟨q⟩ := plane_long_paired_backward_shift h e hz hk hb u hR p
  obtain ⟨r⟩ := plane_long_paired_backward_shift h e hz hk hb u hR q.path
  obtain ⟨t⟩ := plane_long_paired_backward_shift h e hz hk hb u hR r.path
  have hr := plane_long_paired_shift_commutator h e hz hk hb u hR q.path r
  have ht := plane_long_paired_shift_commutator h e hz hk hb u hR r.path t
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let R₄ := ⁅Z Rg r.start,Z Rg z₄⁆
  have hR₄Z : R₄ ≤ Z Rg z₄ :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hR₄V : R₄ ≤ centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) :=
    (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z₄ r.path.end_color))).trans
        (centralizer_le (V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color
          (by change 2 < sourceDistance h; omega)))
  have hnear : (cosetGraph Rg).dist z₄ a' ≤ 4 := by
    have h₁ : (cosetGraph Rg).dist z₄ (p.walk.getVert (p.walk.length-2))=2 := by
      rw [q.path.dist_end]
      have hl : q.path.walk.length=sourceDistance h := q.path.length_eq_b
      omega
    have h₂ : (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a'=2 := by
      rw [p.dist_end]
      have hl : p.walk.length=sourceDistance h := p.length_eq_b
      omega
    have hh := (cosetGraph_connected Rg).dist_triangle
      (u := z₄) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hR₄end : R₄ ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) := by
    apply (hR₄Z.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical z₄ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a' p.end_color)))
    rw [(sourceGeometry h).distance_constant z₄ r.path.end_color]
    change (cosetGraph Rg).dist z₄ a' < sourceDistance h
    omega
  exact ⟨q,r,t,hr.1,ht.1,le_inf hr.2.1 hr.2.2.1,le_inf ht.2.1 ht.2.2.1,
    sup_le hR₄V ht.2.2.2.2.1,hR₄end,hr.2.2.2.2.2,ht.2.2.2.2.2⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
