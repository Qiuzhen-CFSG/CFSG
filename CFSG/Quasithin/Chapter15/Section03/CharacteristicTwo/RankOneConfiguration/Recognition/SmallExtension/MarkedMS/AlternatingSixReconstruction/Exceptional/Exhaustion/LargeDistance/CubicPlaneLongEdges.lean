module
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongChains
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongChains

/-!
# Paired shifts retaining their original first edge

The original plane selector places both selected endpoint seeds inside the
first-edge kernel. Together with endpoint generation this makes the original
and selected edge kernels generate the component stabilizer. Its component
switch normalizes that first-edge kernel. These data survive both orientations
and transport on the actual original graph, with its cubic kernel retained.

The first-edge and selected seeds have central intersection. Consecutive
critical lines are therefore disjoint and generate a literal four-group in
the centralizer of the common endpoint radius.

Source: Meierfrankenfeld--Stellmacher (1993), (5.6)--(5.11), pp.917--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
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

/-- A paired backward shift whose selected kernel also generates with
its parent's literal first-edge kernel. -/
structure EdgePlanePairedBackwardShift {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    extends PlanePairedBackwardShift (h := h) p where
  first_kernel_generation : Q Rg (p.walk.getVert 1) ⊔ Q Rg edge =
    stabilizer Rg a
  first_normalizes : cubic ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))

/-- Transport preserves the same paired generators, conjugated by the
literal graph action, together with the parent walk and every overlap. -/
theorem EdgePlanePairedBackwardShift.conjugate {a a' : Vertex Rg}
    {p : CriticalPath Rg (sourceGeometry h) a a'}
    (q : EdgePlanePairedBackwardShift (h := h) p) (j : FreeAmalgam Rg) :
    Nonempty (EdgePlanePairedBackwardShift (h := h) (p.act j)) := by
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
  refine ⟨⟨⟨act Rg j q.start,act Rg j q.edge,f q.transporter,hstab,
    ?_,?_,(adjacent_act_iff Rg j _ _).mpr q.adjacent_start,
    (adjacent_act_iff Rg j _ _).mpr q.adjacent_shift,
    f q.cubic,hcubic,?_,?_,w,hw1,hwo⟩,?_,?_⟩⟩
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act Rg j) q.first_eq
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act Rg j) q.start_eq
  · have hh := congrArg (Subgroup.map f) q.kernel_generation
    rw [Subgroup.map_sup,map_conj_conj] at hh
    simpa only [Q_act,stabilizer_act,f,inv_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply] using hh
  · have hh := congrArg (Subgroup.map f) q.endpoint_generation
    simpa only [Subgroup.map_sup,hact,Q_act,Z_act,stabilizer_act,f] using hh

  · have hh := congrArg (Subgroup.map f) q.first_kernel_generation
    simpa only [Subgroup.map_sup,Q_act,stabilizer_act,CriticalPath.act,actWalk_getVert,f] using hh

  · simp only [CriticalPath.act,actWalk_getVert,Q_act]
    exact le_normalizer_map f (mem_map_of_mem _ q.first_normalizes)

variable (h e hz hk)

include h e hz hk in
private theorem edge_paired_backward_shift_base
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    Nonempty (EdgePlanePairedBackwardShift (h := h) p) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall := plane_long_critical_image_small h e hz hk hb u hR p
  obtain ⟨t,hat,r,hr,q,hq,_,hgen,hpair,hxAnchor,hinside,g,hg,hgt,_,halt⟩ :=
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
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hfirst] at hxAnchor hinside
  change x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) at hxAnchor
  change Z Rg a' ⊔ Z Rg (act Rg x a') ≤ Q Rg (p.walk.getVert 1) at hinside
  have hanchor : Q Rg (p.walk.getVert 1) ⊔ Q Rg t = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm Rg hfirst))
        (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_right ((le_sup_left.trans hinside).trans le_sup_left))
        ((le_sup_right.trans hinside).trans le_sup_left)
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
  · exact ⟨⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hpair0,hgen,v,hvt,hover⟩,
      hanchor,hxAnchor⟩⟩
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
    refine ⟨⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,w,hw1,hwo⟩,
      ?_,inv_mem hxAnchor⟩⟩
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

    · have hQfirst : (Q Rg (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q Rg (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hG,Q_act,inv_inv] using hh

private theorem edge_paired_backward_shift_of_vertices
    {a a' c c' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : CriticalPath Rg (sourceGeometry h) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (EdgePlanePairedBackwardShift (h := h) q)) :
    Nonempty (EdgePlanePairedBackwardShift (h := h) p) := by
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
  exact ⟨⟨⟨r.start,r.edge,r.transporter,r.transporter_mem,
    by simpa only [hv] using r.first_eq,by simpa only [hv] using r.start_eq,
    r.adjacent_start,r.adjacent_shift,r.cubic,r.cubic_mem,
    r.kernel_generation,r.endpoint_generation,w,hw1,hwo⟩,by
      simpa only [hv] using r.first_kernel_generation,by
      simpa only [hv] using r.first_normalizes⟩⟩

include h e hz hk in
/-- Repeated selection retains the original-edge generating join and
both earlier generating pairs at every vertex, with no additional premise. -/
theorem plane_long_edge_paired_backward_shift
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    Nonempty (EdgePlanePairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg j⁻¹ a = alpha Rg := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := edge_paired_backward_shift_base h e hz hk
    hb u hR (a' := act Rg j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex Rg) : act Rg j (act Rg j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact edge_paired_backward_shift_of_vertices h p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)


variable {h e hz hk}

/-- The two literal edge seeds have only central intersection, because their
full edge kernels generate the intervening component stabilizer. -/
theorem EdgePlanePairedBackwardShift.edge_seed_intersection_central
    {a a' : Vertex Rg}
    {p : CriticalPath Rg (sourceGeometry h) a a'}
    (q : EdgePlanePairedBackwardShift (h := h) p) :
    Z Rg (p.walk.getVert 1) ⊓ Z Rg q.edge ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hcent {t : Vertex Rg} (ht : Adjacent Rg a t) :
      Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    have hcol : color Rg t = true := by
      have hh := adjacent_color_ne Rg ht
      rw [p.start_color] at hh
      cases he : color Rg t <;> simp_all
    intro x hx
    rw [Z,if_neg (by simp [hcol])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mpr
  rw [←q.first_kernel_generation]
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (hcent hat)))
    (le_centralizer_iff.mp (inf_le_right.trans (hcent q.adjacent_start)))

variable (h e hz hk)

include h e hz hk in
/-- The original critical line misses the selected backward edge seed.
This uses the original and selected kernels together; a single endpoint
transposition is not asserted to generate the stabilizer. -/
theorem plane_long_edge_paired_critical_line_disjoint
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : EdgePlanePairedBackwardShift (h := h) p) :
    ⁅Z Rg a,Z Rg a'⁆ ⊓ Z Rg q.edge = ⊥ := by
  let H := ⁅Z Rg a,Z Rg a'⁆
  have hfirst : H ≤ Z Rg (p.walk.getVert 1) :=
    plane_critical_commutator_le_first_seed h e hz hk u hR p
  have hcard : Nat.card H = 2 :=
    (plane_long_critical_indices_two h e hz hk hb u hR p).2.2
  have hnc : ¬ H ≤ Z Rg q.edge := by
    intro hh
    exact critical_commutator_not_central h e hz hk p
      ((le_inf hfirst hh).trans q.edge_seed_intersection_central)
  let := finite_Z Rg (p.walk.getVert 1)
  let : Finite H := Finite.of_injective (inclusion hfirst) (inclusion_injective _)
  let : Finite (H ⊓ Z Rg q.edge : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  by_contra hne
  have hp := (one_lt_card_iff_ne_bot (H ⊓ Z Rg q.edge)).mpr hne
  have he : H ⊓ Z Rg q.edge = H := eq_of_le_of_card_ge inf_le_left (by omega)
  exact hnc (he ▸ inf_le_right)

include h e hz hk in
/-- Successive selected critical lines are independent in the same full
seed, and their join has order four on both central covers. -/
theorem plane_long_edge_paired_critical_plane
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : EdgePlanePairedBackwardShift (h := h) p) :
    let H := ⁅Z Rg a,Z Rg a'⁆
    let K := ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆
    H ⊓ K = ⊥ ∧ H ⊔ K ≤ Z Rg a ∧ Nat.card (H ⊔ K : Subgroup (FreeAmalgam Rg)) = 4 := by
  let H := ⁅Z Rg a,Z Rg a'⁆
  let K := ⁅Z Rg q.start,Z Rg (p.walk.getVert (p.walk.length-2))⁆
  have hs := plane_long_paired_shift_commutator h e hz hk
    hb u hR p q.toPlanePairedBackwardShift
  have hHZ : H ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant a p.start_color]
            exact sourceDistance_pos h) p.critical).trans (Z_normalized Rg a))
  have hKZ : K ≤ Z Rg a := hs.2.2.1
  have hdis : H ⊓ K = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left H hs.2.1).trans_eq
      (plane_long_edge_paired_critical_line_disjoint h e hz hk hb u hR p q)
  have hHK : K ≤ centralizer (H : Set (FreeAmalgam Rg)) := by
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
    exact (hKZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans (centralizer_le hHZ)
  have hcH : Nat.card H = 2 :=
    (plane_long_critical_indices_two h e hz hk hb u hR p).2.2
  have hcK : Nat.card K = 2 := hs.1
  refine ⟨hdis,sup_le hHZ hKZ,?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint H K
    (hHK.trans (Subgroup.centralizer_le_normalizer (H : Set (FreeAmalgam Rg)))) (disjoint_iff.mpr hdis),hcH,hcK]

include h e hz hk in
/-- The source R₄/R₆ configuration now has an actual four-group in the
centralizer of the common endpoint radius, with both original-edge joins
retained. This does not assert intermediate-stabilizer noncentrality. -/
theorem plane_long_edge_paired_terminal_plane
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ q : EdgePlanePairedBackwardShift (h := h) p,
      ∃ r : EdgePlanePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePlanePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z Rg r.start,Z Rg z₄⁆
          let R₆ := ⁅Z Rg t.start,Z Rg z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam Rg)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z Rg r.start ⊓
            centralizer (V Rg z₄ : Set (FreeAmalgam Rg)) := by
  obtain ⟨q⟩ := plane_long_edge_paired_backward_shift h e hz hk hb u hR p
  obtain ⟨r⟩ := plane_long_edge_paired_backward_shift h e hz hk hb u hR q.path
  obtain ⟨t⟩ := plane_long_edge_paired_backward_shift h e hz hk hb u hR r.path
  have hp := plane_long_edge_paired_critical_plane h e hz hk hb u hR r.path t
  have ht := plane_long_paired_shift_commutator h e hz hk
    hb u hR r.path t.toPlanePairedBackwardShift
  have hR₄Z : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z Rg (q.path.walk.getVert (q.path.walk.length-2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans
        (Z_normalized Rg _))
  have hR₄V := (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ r.path.end_color))).trans
    (centralizer_le (V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color
      (by change 2 < sourceDistance h; omega)))
  exact ⟨q,r,t,hp.1,hp.2.2,le_inf hp.2.1 (sup_le hR₄V ht.2.2.2.2.1)⟩


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
