module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedEdges
/-!
# Strict cube intersections on the compatible backward path

The full component seed has index four over any incident edge seed in the
three-pair case. A strict Baumann slice therefore forces the intersection of
two neighboring component seeds to be exactly their common edge seed. The
original and selected edge cores generate the component stabilizer, so their
compatible triple-seed intersection is central there.

The final application orients the simultaneous cubic choice back over the
original critical path. It retains the strict slice, both actor generation,
the original-edge generating pair and cubic normality, and supplies the actual
central backward triple needed in the small-kernel normalization argument.
Both moving covers and all central attachments remain in the full seeds.

Source: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6) and the equal-mover part of (5.12)(1),(3), pp.917,924–927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
theorem cube_strict_seed_intersection_eq_edge
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c = Z d.radical t := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  let W := Z d.radical a ⊓ Z d.radical c
  have hTW : Z d.radical t ≤ W :=
    le_inf (adjacent_Z_le d.radical ha hat) (adjacent_Z_le d.radical hc hct)
  have hindex : (Z d.radical t).relIndex (Z d.radical c) = 4 :=
    cube_edge_seed_index s u hfull hc hct
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hWB : W ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    inf_le_left.trans (Escape.EdgeTransfer.Z_le_B hb a ha)
  have hWi : 2 < W.relIndex (Z d.radical c) :=
    hstrict.trans_le ((relIndex_le_of_le_left hWB index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c) index_ne_zero_of_finite))
  have hm := relIndex_mul_relIndex (Z d.radical t) W (Z d.radical c) hTW inf_le_right
  rw [hindex] at hm
  have hpos : 0 < (Z d.radical t).relIndex W :=
    Nat.pos_of_ne_zero (by intro he; rw [he,zero_mul] at hm; omega)
  have hone : (Z d.radical t).relIndex W = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hone) hTW

include s in
theorem cube_strict_compatible_triple_central
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a v c b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) (hvb : Adjacent d.radical v b)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict0 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical v))
    (hstrict1 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hgen : Q d.radical b ⊔ Q d.radical t = stabilizer d.radical a) :
    Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have h0 := cube_strict_seed_intersection_eq_edge s hb u hfull ha hab hvb hstrict0
  have h1 := cube_strict_seed_intersection_eq_edge s hb u hfull ha hat hct hstrict1
  have hcent {w : Vertex d.radical} (haw : Adjacent d.radical a w) :
      Z d.radical w ≤ centralizer (Q d.radical w : Set (FreeAmalgam d.radical)) := by
    have hw : color d.radical w = true := by
      have hh := adjacent_color_ne d.radical haw
      rw [ha] at hh
      cases he : color d.radical w <;> simp_all
    intro x hx
    rw [Z,if_neg (by simp [hw])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mpr
  rw [←hgen]
  apply sup_le
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
      (h0.le.trans (hcent hab))
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      (h1.le.trans (hcent hat))

include e hz hn in
theorem cube_strict_backward_shift_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hanchor,hxAnchor,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    ElementarySmallCompatible.cube_compatible_strict_backward_pair_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hdelta hstrict
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hx3,hpair,hgen,v,hvt,hover⟩,hanchor⟩,hi,hxAnchor⟩
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
    refine ⟨⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,?_,w,hw1,hwo⟩,?_⟩,?_,?_⟩
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

    · have hQfirst : (Q d.radical (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q d.radical (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hGa,Q_act,inv_inv] using hh

    · have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
          (MulAut.conj x).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          hb2 (alpha d.radical) rfl hxG)
      change 2 < (B d.radical (alpha d.radical) _).relIndex
        (U d.radical (act d.radical y (p.walk.getVert 2)))
      rw [←hstart,U_act,inv_inv,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
      exact hi
    · exact inv_mem hxAnchor

include e hz hn in
/-- The literal compatible cube shift has a central backward triple. -/
theorem cube_strict_backward_triple_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      Z d.radical q.start ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert 2) ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hN⟩ := cube_strict_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
    hb u him p hstrict
  refine ⟨q,hq,hN,?_⟩
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hc := cube_strict_compatible_triple_central s hb2 u hfull rfl hat hct
    q.adjacent_start q.adjacent_shift hstrict hq q.first_kernel_generation
  have he : Z d.radical q.start ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert 2) =
      Z d.radical (p.walk.getVert 2) ⊓ Z d.radical (alpha d.radical) ⊓ Z d.radical q.start := by ac_rfl
  rwa [he]

private theorem conjugate_shift_with_vertices {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : EdgePairedBackwardShift (h := h) p) (j : FreeAmalgam d.radical) :
    ∃ r : EdgePairedBackwardShift (h := h) (p.act j),
      r.start = act d.radical j q.start ∧
      r.cubic = (MulAut.conj j⁻¹) q.cubic := by
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
  refine ⟨⟨⟨act d.radical j q.start,act d.radical j q.edge,f q.transporter,hstab,
    ?_,?_,(adjacent_act_iff d.radical j _ _).mpr q.adjacent_start,
    (adjacent_act_iff d.radical j _ _).mpr q.adjacent_shift,
    f q.cubic,hcubic,?_,?_,?_,w,hw1,hwo⟩,?_⟩,rfl,rfl⟩
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.first_eq
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.start_eq
  · rw [Q_act,←map_pow]
    exact mem_map_of_mem _ q.cubic_pow
  · have hh := congrArg (Subgroup.map f) q.kernel_generation
    rw [Subgroup.map_sup,map_conj_conj] at hh
    simpa only [Q_act,stabilizer_act,f,inv_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply] using hh
  · have hh := congrArg (Subgroup.map f) q.endpoint_generation
    simpa only [Subgroup.map_sup,hact,Q_act,Z_act,stabilizer_act,f] using hh

  · have hh := congrArg (Subgroup.map f) q.first_kernel_generation
    simpa only [Subgroup.map_sup,Q_act,stabilizer_act,CriticalPath.act,actWalk_getVert,f] using hh

private theorem shift_of_vertices
    {a a' c c' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (r : EdgePairedBackwardShift (h := h) q) :
    ∃ r' : EdgePairedBackwardShift (h := h) p,
      r'.start = r.start ∧ r'.cubic = r.cubic := by
  subst c
  subst c'
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
  exact ⟨⟨⟨r.start,r.edge,r.transporter,r.transporter_mem,
    by simpa only [hv] using r.first_eq,by simpa only [hv] using r.start_eq,
    r.adjacent_start,r.adjacent_shift,r.cubic,r.cubic_mem,r.cubic_pow,
    r.kernel_generation,r.endpoint_generation,w,hw1,hwo⟩,by
      simpa only [hv] using r.first_kernel_generation⟩,rfl,rfl⟩

include e hz hn in
/-- The strict compatible cube shift at every original component vertex. -/
theorem cube_strict_backward_triple_at_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      q.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
      Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base : ∀ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j⁻¹ a) (act d.radical j⁻¹ z),
      2 < (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) →
      ∃ q : EdgePairedBackwardShift (h := h) r,
        2 < (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical q.start) ∧
        q.cubic ∈ normalizer (Q d.radical (r.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
    rw [hbase]
    intro r hr
    exact cube_strict_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb u him r hr
  have hstrict' : 2 < (B d.radical (act d.radical j⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act j⁻¹).walk.getVert 2)) := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb2 j⁻¹ a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (j⁻¹)⁻¹).injective]
    exact hstrict
  obtain ⟨q,hq,hN⟩ := base (p.act j⁻¹) hstrict'
  obtain ⟨r,hrs,hrx⟩ := conjugate_shift_with_vertices q j
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  obtain ⟨w,hws,hwx⟩ := shift_of_vertices p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel z) (by intro i; simp only [CriticalPath.act,actWalk_getVert,hcancel]) r
  have hwi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical w.start) := by
    rw [hws,hrs]
    have hB := Escape.PairingControl.FirstPairing.B_act (geometry := replacementGeometry h d) hb2 j (act d.radical j⁻¹ a)
      ((action_preserves_color d.radical j⁻¹ a).trans p.start_color)
    rw [hcancel a] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
    exact hq
  have hwN : w.cubic ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
    rw [hwx,hrx]
    have hh := le_normalizer_map (MulAut.conj j⁻¹).toMonoidHom (mem_map_of_mem _ hN)
    change (MulAut.conj j⁻¹) q.cubic ∈ normalizer
      ((Q d.radical ((p.act j⁻¹).walk.getVert 1)).map (MulAut.conj j⁻¹).toMonoidHom : Set _) at hh
    rw [←Q_act] at hh
    simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
  refine ⟨w,hwi,hwN,?_⟩
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hc := cube_strict_compatible_triple_central s hb2 u hfull p.start_color hat hct
    w.adjacent_start w.adjacent_shift hstrict hwi w.first_kernel_generation
  have he : Z d.radical w.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) =
      Z d.radical (p.walk.getVert 2) ⊓ Z d.radical a ⊓ Z d.radical w.start := by ac_rfl
  rwa [he]


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
