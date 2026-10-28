module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedGeneratedPath
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEndpoint
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedExclusion

/-!
# Compatible strict mixed-plane backward selection at distance four

A crossing mixed plane simultaneously gives generation by two edge kernels
and generation by the selected relative normalizer and the critical seed.
Since every critical image is small at distance four, strict backward escape
applies to this same selected edge. The result retains the local transporter,
the edge transporter, and their agreement on the full selected edge kernel.
The strict slice is preserved, so the compatible triple is fixed at the
shared component vertex. All selections stay on the original graph and
use the literal symmetric quotient; both moving covers and full central
attachments remain present.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the paired selections and fixed-line argument in (5.12)(1),
printed pp.924--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Select one backward edge with both the relative-normalizer generation
needed for escape and generation by its full kernel and the original first
edge kernel. The latter is an additional geometric selection, not a
consequence of arbitrary relative-normalizer generation. -/
theorem mixed_small_aligned_generating_neighbor_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  obtain ⟨E,v,hEm,hEk,hEi⟩ := MixedEndpoint.edge_preimage s u hf hat
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hAE : A ≤ E := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rwa [hAm,hEm]
  obtain ⟨a,ha,hAi⟩ := small_critical_image_eq_swap s hc p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
  change A.map s.projection = zpowers a at hAi
  have haE : a ∈ plus.map (MulAut.conj v).toMonoidHom := by
    rw [←hEi]
    exact (map_mono hAE) (hAi ▸ mem_zpowers a)
  obtain ⟨k,hpair,hNg⟩ := MixedGeneratedPath.mixed_aligned_pair v a haE ha
  obtain ⟨g,hgk⟩ := s.surjective k
  let D := E.map (MulAut.conj g).toMonoidHom
  have hDi : D.map s.projection = (plus.map (MulAut.conj v).toMonoidHom).map
      (MulAut.conj k).toMonoidHom := by
    rw [show D=E.map (MulAut.conj g).toMonoidHom from rfl,MixedGeneratedPath.map_conj_map,hEi,hgk]
  have hDk : s.projection.ker ≤ D := by
    have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top _)
    rw [s.projection_kernel,←hQ]
    apply map_mono
    rwa [←s.projection_kernel]
  have hgen : E ⊔ D = ⊤ := by
    apply map_injective_of_ker_le s.projection (hEk.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEi,hDi,map_top_of_surjective _ s.surjective]
    exact hpair
  have hNm : (normalizer (D : Set d.overgroup)).map s.projection =
      normalizer (D.map s.projection : Set S) := by
    calc
      _ = ((normalizer (D.map s.projection : Set S)).comap s.projection).map s.projection := by
        rw [comap_normalizer_eq_of_surjective _ s.surjective,comap_map_eq_self hDk]
      _ = _ := map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr s.surjective]; exact le_top)
  have hNgen : normalizer (D : Set d.overgroup) ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection ((hDk.trans D.le_normalizer).trans le_sup_left) le_top
    rw [Subgroup.map_sup,hNm,hDi,hAi,map_top_of_surjective _ s.surjective]
    exact hNg
  let f := (embedM d.radical g)⁻¹
  have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range := stabilizer_m_base d.radical
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := by
    change f ∈ stabilizer d.radical (alpha d.radical)
    rw [hbase]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hDm : D.map (embedM d.radical) = Q d.radical (act d.radical f (p.walk.getVert 1)) := by
    rw [show D=E.map (MulAut.conj g).toMonoidHom from rfl,MixedGeneratedPath.map_conj_map,hEm,Q_act]
    simp only [f,inv_inv]
  refine ⟨act d.radical f (p.walk.getVert 1),?_,?_,?_⟩
  · simpa only [hfix] using (adjacent_act_iff d.radical f _ _).mpr hat
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rwa [Subgroup.map_sup,hEm,hDm,←MonoidHom.range_eq_map,←hbase] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hNgen
    rwa [Subgroup.map_sup,SylowNormalizer.normalizer_embed,hDm,hAm,
      ←MonoidHom.range_eq_map,←hbase] at hh

/-- A selected path retains both geometric transporters and the original
local actor whose action the edge holomorph realizes. -/
structure MixedBackwardShift {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') where
  start : Vertex d.radical
  edge : Vertex d.radical
  localActor : FreeAmalgam d.radical
  local_mem : localActor ∈ stabilizer d.radical a
  first_eq : act d.radical localActor (p.walk.getVert 1) = edge
  edgeActor : FreeAmalgam d.radical
  edge_mem : edgeActor ∈ stabilizer d.radical edge
  start_eq : act d.radical edgeActor (act d.radical localActor (p.walk.getVert 2)) = start
  originalActor : FreeAmalgam d.radical
  original_mem : originalActor ∈ stabilizer d.radical a
  agreement : ∀ v ∈ Q d.radical edge,
    (MulAut.conj edgeActor⁻¹) v = (MulAut.conj originalActor) v
  adjacent_start : Adjacent d.radical a edge
  path : CriticalPath d.radical (replacementGeometry h d) start
    (p.walk.getVert (p.walk.length-2))
  first : path.walk.getVert 1 = edge
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert (i+2) = p.walk.getVert i
  generation : Q d.radical edge ⊔ Q d.radical (p.walk.getVert 1) = stabilizer d.radical a

  index_eq : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical start) =
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))
  relative_generation :
    (normalizer (Q d.radical edge : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) ⊔
      Z d.radical a' = stabilizer d.radical a

theorem mixed_strict_backward_shift_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    Nonempty (MixedBackwardShift (h := h) p) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hb2 : 2 < replacementDistance h d := by omega
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hpair,hgen⟩ := mixed_small_aligned_generating_neighbor_knownSimple hb u him p
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hfirst hat
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 _ rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  obtain ⟨k,hk,q,hq1,hover,hidx,g,hg,hagree⟩ := MixedExclusion.relative_shift_with_agreement s hc hb2 u hf p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    hat hct hgen (by rwa [hi])
  exact ⟨⟨_,t,x,hx,hxt,k,hk,rfl,g,hg,hagree,hat,q,hq1,hover,(sup_comm _ _).trans hpair,hidx.trans hi,hgen⟩⟩

theorem MixedBackwardShift.interior_generation {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : MixedBackwardShift (h := h) p) (hb : 2 < replacementDistance h d) :
    Q d.radical (q.path.walk.getVert 1) ⊔ Q d.radical (q.path.walk.getVert 3) =
      stabilizer d.radical (q.path.walk.getVert 2) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have he : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  rw [q.first,q.overlap 1 (by omega),he]
  exact q.generation

private theorem MixedBackwardShift.conjugate {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : MixedBackwardShift (h := h) p) (hb : 2 < replacementDistance h d)
    (j : FreeAmalgam d.radical) :
    Nonempty (MixedBackwardShift (h := h) (p.act j)) := by
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hact (x : FreeAmalgam d.radical) (v : Vertex d.radical) :
      act d.radical (f x) (act d.radical j v) = act d.radical j (act d.radical x v) := by
    simp only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,←act_mul]
    congr 1
    group
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
  refine ⟨⟨act d.radical j q.start,act d.radical j q.edge,
    f q.localActor,?_,?_,f q.edgeActor,?_,?_,f q.originalActor,?_,?_,
    (adjacent_act_iff d.radical j _ _).mpr q.adjacent_start,w,hw1,hwo,?_,?_,?_⟩⟩
  · rw [stabilizer_act]
    exact mem_map_of_mem _ q.local_mem
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.first_eq
  · rw [stabilizer_act]
    exact mem_map_of_mem _ q.edge_mem
  · simpa only [CriticalPath.act,actWalk_getVert,hact] using congrArg (act d.radical j) q.start_eq
  · rw [stabilizer_act]
    exact mem_map_of_mem _ q.original_mem
  · intro v hv
    rw [Q_act] at hv
    obtain ⟨v,hv,rfl⟩ := hv
    have he := congrArg f (q.agreement v hv)
    change f (q.edgeActor⁻¹*v*(q.edgeActor⁻¹)⁻¹) = f (q.originalActor*v*q.originalActor⁻¹) at he
    change (f q.edgeActor)⁻¹ * f v * ((f q.edgeActor)⁻¹)⁻¹ =
      f q.originalActor * f v * (f q.originalActor)⁻¹
    simpa only [map_mul,map_inv] using he
  · have he := congrArg (Subgroup.map f) q.generation
    simpa only [Subgroup.map_sup,Q_act,stabilizer_act,CriticalPath.act,actWalk_getVert,f] using he

  · simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb j a p.start_color,
      U_act,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective,
      relIndex_map_map_of_injective _ _ (MulAut.conj j⁻¹).injective]
    exact q.index_eq
  · have he := congrArg (Subgroup.map f) q.relative_generation
    simpa only [Subgroup.map_sup,Subgroup.map_inf _ _ f (MulAut.conj j⁻¹).injective,
      map_normalizer_eq_of_bijective (f := f) _ (MulAut.conj j⁻¹).bijective,
      Q_act,Z_act,stabilizer_act,f] using he

private theorem mixed_shift_of_vertices
    {a a' c c' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (MixedBackwardShift (h := h) q)) : Nonempty (MixedBackwardShift (h := h) p) := by
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
  exact ⟨⟨r.start,r.edge,r.localActor,r.local_mem,
    by simpa only [hv] using r.first_eq,r.edgeActor,r.edge_mem,
    by simpa only [hv] using r.start_eq,r.originalActor,r.original_mem,
    r.agreement,r.adjacent_start,w,hw1,hwo,by simpa only [hv] using r.generation,
    by simpa only [hv] using r.index_eq,r.relative_generation⟩⟩

theorem mixed_strict_backward_shift_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    Nonempty (MixedBackwardShift (h := h) p) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := mixed_strict_backward_shift_knownSimple hb u him (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hstrict' : 2 < (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act g⁻¹).walk.getVert 2)) := by
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act (geometry := replacementGeometry h d) (show 2 < replacementDistance h d by omega) g⁻¹ a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hstrict
  obtain ⟨q⟩ := base (p.act g⁻¹) hstrict'
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact mixed_shift_of_vertices p ((p.act g⁻¹).act g)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate (by omega) g)

theorem MixedBackwardShift.adjacent_shift {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : MixedBackwardShift (h := h) p) : Adjacent d.radical q.start q.edge := by
  have hl : 0 < q.path.walk.length := q.path.length_eq_b ▸ replacementDistance_pos h d
  have hh := q.path.walk.adj_getVert_succ (i := 0) hl
  rw [SimpleGraph.Walk.getVert_zero,q.first] at hh
  exact (cosetGraph_adj d.radical _ _).mp hh

theorem MixedBackwardShift.edge_color {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : MixedBackwardShift (h := h) p) : color d.radical q.edge=true := by
  have hh := adjacent_color_ne d.radical q.adjacent_start
  rw [p.start_color] at hh
  cases he : color d.radical q.edge <;> simp_all

/-- The selected mixed shift preserves the strict slice and supplies the
actual central backward triple on every component vertex. -/
theorem mixed_strict_backward_triple_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical q.start) ∧
      Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := mixed_strict_backward_shift_at_knownSimple hb u him p hstrict
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by rwa [q.index_eq]
  refine ⟨q,hi,?_⟩
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hh := mixed_strict_compatible_triple_central s hb2 u hf p.start_color
    q.adjacent_start q.adjacent_shift hat hvt hi hstrict q.generation
  exact hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
