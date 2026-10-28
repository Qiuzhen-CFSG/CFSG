module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeLargeExclusion

/-!
# Coherent paired backward chains on the original nonsylow graph

The strict small-image selector retains two generating joins: the selected
edge kernel with its cubic conjugate, and the kernel with both endpoint
seeds. Its backward path can initially lie over either the given critical
path or the same cubic conjugate of that path. In the second orientation,
conjugate the whole configuration back and invert the cubic. The kernel
join then exchanges its two factors, and the endpoint join exchanges its
two seeds. Thus both joins survive on the original path, together with the
actual neighbor transporter, cubic lift and every overlap vertex.

The construction is equivariant under the literal right graph action:
transport by j conjugates every group element by j⁻¹. The proved global
small-image and strict-slice results discharge the selection premises at
every original component vertex. No single-endpoint generating shift is
asserted or needed to iterate this paired construction.

Three successive choices give the source R₄ and R₆ configuration. Each
full critical commutator has order two and lies in its selected edge seed
and the preceding component seed. Quadratic three-pair action centralizes
the selected kernel. Distance bounds place both R₄ and R₆ in the centralizer
of the full radius at the R₄ endpoint; R₄ also centralizes the original
endpoint seed. Their own critical stabilizers do not centralize these lines.
The source's stronger intermediate-stabilizer noncentrality, strict endpoint
radius estimate and terminal contradiction remain separate obligations.

All statements concern the original minimum characteristic replacement,
including its nonsylow radical, both covers of orders sixteen and thirty-two,
and arbitrary central attachments. No exceptional graph is identified with
this graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)--(5.11), printed pp.917--924, especially the repeated selection
before (5.11) and the simultaneous R₄/R₆ centralization on p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The simultaneous two-kernel and two-endpoint choice, oriented over the
original critical path. This has no single-endpoint generation field. -/
structure PairedBackwardShift {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') where
  start : Vertex d.radical
  edge : Vertex d.radical
  transporter : FreeAmalgam d.radical
  transporter_mem : transporter ∈ stabilizer d.radical a
  first_eq : act d.radical transporter (p.walk.getVert 1) = edge
  start_eq : act d.radical transporter (p.walk.getVert 2) = start
  adjacent_start : Adjacent d.radical a edge
  adjacent_shift : Adjacent d.radical start edge
  cubic : FreeAmalgam d.radical
  cubic_mem : cubic ∈ Ltilde d.radical a
  cubic_pow : cubic^3 ∈ Q d.radical a
  kernel_generation : Q d.radical edge ⊔
    (Q d.radical edge).map (MulAut.conj cubic).toMonoidHom = stabilizer d.radical a
  endpoint_generation : Q d.radical edge ⊔ Z d.radical a' ⊔
    Z d.radical (act d.radical cubic a') = stabilizer d.radical a
  path : CriticalPath d.radical (replacementGeometry h d) start
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
theorem PairedBackwardShift.conjugate {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : PairedBackwardShift (h := h) p) (j : FreeAmalgam d.radical) :
    Nonempty (PairedBackwardShift (h := h) (p.act j)) := by
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hact (x : FreeAmalgam d.radical) (v : Vertex d.radical) :
      act d.radical (f x) (act d.radical j v) = act d.radical j (act d.radical x v) := by
    simp only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,←act_mul]
    congr 1
    group
  have hstab : f q.transporter ∈ stabilizer d.radical (act d.radical j a) := by
    rw [stabilizer_act]
    exact mem_map_of_mem _ q.transporter_mem
  have hcubic : f q.cubic ∈ Ltilde d.radical (act d.radical j a) := by
    rw [Ltilde_act]
    exact mem_map_of_mem _ q.cubic_mem
  have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j q.start) ((p.act j).walk.getVert ((p.act j).walk.length-2)),
      w.walk.getVert 1=act d.radical j q.edge ∧
      ∀ i ≤ (p.act j).walk.length-2, w.walk.getVert (i+2)=(p.act j).walk.getVert i := by
    have hend : (p.act j).walk.getVert ((p.act j).walk.length-2) =
        act d.radical j (p.walk.getVert (p.walk.length-2)) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert]
    rw [hend]
    refine ⟨q.path.act j,?_,?_⟩
    · simp only [CriticalPath.act,actWalk_getVert,q.first]
    · intro i hi
      have hi0 : i ≤ p.walk.length-2 := by
        simpa only [CriticalPath.act,actWalk_length] using hi
      simp only [CriticalPath.act,actWalk_getVert,q.overlap i hi0]
  obtain ⟨w,hw1,hwo⟩ := hex
  refine ⟨⟨act d.radical j q.start,act d.radical j q.edge,f q.transporter,hstab,
    ?_,?_,(adjacent_act_iff d.radical j _ _).mpr q.adjacent_start,
    (adjacent_act_iff d.radical j _ _).mpr q.adjacent_shift,
    f q.cubic,hcubic,?_,?_,?_,w,hw1,hwo⟩⟩
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.first_eq
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.start_eq
  · rw [Q_act,←map_pow]
    exact mem_map_of_mem _ q.cubic_pow
  · have hh := congrArg (Subgroup.map f) q.kernel_generation
    rw [Subgroup.map_sup,map_conj_conj] at hh
    simpa only [Q_act,stabilizer_act,f,inv_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply] using hh
  · have hh := congrArg (Subgroup.map f) q.endpoint_generation
    simpa only [Subgroup.map_sup,hact,Q_act,Z_act,stabilizer_act,f] using hh

include e hz hn in
private theorem paired_backward_shift_base
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    Nonempty (PairedBackwardShift (h := h) p) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).1]
    decide
  obtain ⟨t,hat,g,hg,hgt,hct,_,x,hx,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    nonsylow_strict_small_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hsmall hdelta
      (nonsylow_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p)
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hx3,hpair,hgen,v,hvt,hover⟩⟩
  · let y := g*x⁻¹
    have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hxG)
    have hfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hxG
    have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
      rw [←hfix]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)) =
        act d.radical y (p.walk.getVert 2) := (act_mul d.radical g x⁻¹ _).symm
    have hct' : Adjacent d.radical (act d.radical y (p.walk.getVert 2))
        (act d.radical x⁻¹ t) := by
      rw [←hstart]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 1=act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          simp only [CriticalPath.act,actWalk_getVert,hover i (hlen.symm ▸ hi),hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
    obtain ⟨w,hw1,hwo⟩ := hex
    refine ⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,?_,w,hw1,hwo⟩⟩
    · simpa only [inv_pow] using (Q d.radical (alpha d.radical)).inv_mem hx3
    · rw [Q_act,inv_inv,map_map]
      have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro z
        change x⁻¹*(x*z*x⁻¹)*(x⁻¹)⁻¹=z
        group
      rw [he,map_id]
      exact (sup_comm _ _).trans hpair
    · have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          Q d.radical (act d.radical x⁻¹ t) := by rw [Q_act,inv_inv]
      have hZa (z : Vertex d.radical) : (Z d.radical z).map (MulAut.conj x).toMonoidHom =
          Z d.radical (act d.radical x⁻¹ z) := by rw [Z_act,inv_inv]
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen
      simp only [Subgroup.map_sup,hQt,hZa,hGa,←act_mul,mul_inv_cancel,act_one] at hh
      calc
        _ = Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical (act d.radical x⁻¹ a') ⊔
          Z d.radical a' := by ac_rfl
        _ = _ := hh

private theorem paired_backward_shift_of_vertices
    {a a' c c' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (PairedBackwardShift (h := h) q)) :
    Nonempty (PairedBackwardShift (h := h) p) := by
  subst c
  subst c'
  obtain ⟨r⟩ := hr
  have hl : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d) r.start
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
    r.adjacent_start,r.adjacent_shift,r.cubic,r.cubic_mem,r.cubic_pow,
    r.kernel_generation,r.endpoint_generation,w,hw1,hwo⟩⟩

include e hz hn in
/-- Repeated source selection on the original nonsylow graph retains both
generating pairs at every vertex, with no critical-image or strict-slice premise. -/
theorem nonsylow_paired_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Nonempty (PairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := paired_backward_shift_base (e := e) (hz := hz) (hn := hn)
    hb hns (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact paired_backward_shift_of_vertices p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)

include e hz hn in
/-- The actual shifted critical line has order two, lies in the selected
edge seed and the old starting seed, and centralizes the full old endpoint
radius. Its noncentrality remains at its own starting stabilizer. -/
theorem nonsylow_paired_shift_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p) :
    let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧ H ≤ Z d.radical a ∧
      H ≤ centralizer (Q d.radical q.edge : Set (FreeAmalgam d.radical)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hHt : H ≤ Z d.radical q.edge := by
    simpa only [q.first] using cube_critical_commutator_le_first_seed s hc u hR q.path
  have hHe : H ≤ Z d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q d.radical q.edge : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hVQ : V d.radical a' ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    change (cosetGraph d.radical).dist a' (p.walk.getVert (p.walk.length-2)) + 2 <
      replacementDistance h d
    rw [SimpleGraph.dist_comm,p.dist_end]
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    omega
  have hHV : H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ q.path.end_color))).trans (centralizer_le hVQ)
  exact ⟨(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns q.path).2.2,hHt,hHt.trans (adjacent_Z_le d.radical p.start_color q.adjacent_start),
    hHQ,hHV,critical_commutator_not_central s hc q.path⟩

include e hz hn in
/-- Three simultaneous source choices over one coherent chain. The literal
R₄ and R₆ both centralize the full radius at the R₄ endpoint. Both generating
pairs and the cubic lifts are retained by each shift, including when an
inverse orientation was selected. No centrality at an intermediate
stabilizer is inferred from these radius bounds. -/
theorem nonsylow_three_paired_shifts_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : PairedBackwardShift (h := h) p,
      ∃ r : PairedBackwardShift (h := h) q.path,
        ∃ t : PairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          Nat.card R₄ = 2 ∧ Nat.card R₆ = 2 ∧
          R₄ ≤ Z d.radical r.edge ⊓ Z d.radical q.start ∧
          R₆ ≤ Z d.radical t.edge ⊓ Z d.radical r.start ∧
          R₄ ⊔ R₆ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          R₄ ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) ∧
          ¬ R₄ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
          ¬ R₆ ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := nonsylow_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p
  obtain ⟨r⟩ := nonsylow_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path
  obtain ⟨t⟩ := nonsylow_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns r.path
  have hr := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path r
  have ht := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn) hb hns r.path t
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
  have hR₄Z : R₄ ≤ Z d.radical z₄ :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hR₄V : R₄ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) :=
    (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z₄ r.path.end_color))).trans
        (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
          (by change 2 < replacementDistance h d; omega)))
  have hnear : (cosetGraph d.radical).dist z₄ a' ≤ 4 := by
    have h₁ : (cosetGraph d.radical).dist z₄ (p.walk.getVert (p.walk.length-2))=2 := by
      rw [q.path.dist_end]
      have hl : q.path.walk.length=replacementDistance h d := q.path.length_eq_b
      omega
    have h₂ : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a'=2 := by
      rw [p.dist_end]
      have hl : p.walk.length=replacementDistance h d := p.length_eq_b
      omega
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := z₄) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hR₄end : R₄ ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hR₄Z.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical z₄ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [(replacementGeometry h d).distance_constant z₄ r.path.end_color]
    change (cosetGraph d.radical).dist z₄ a' < replacementDistance h d
    omega
  exact ⟨q,r,t,hr.1,ht.1,le_inf hr.2.1 hr.2.2.1,le_inf ht.2.1 ht.2.2.1,
    sup_le hR₄V ht.2.2.2.2.1,hR₄end,hr.2.2.2.2.2,ht.2.2.2.2.2⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
