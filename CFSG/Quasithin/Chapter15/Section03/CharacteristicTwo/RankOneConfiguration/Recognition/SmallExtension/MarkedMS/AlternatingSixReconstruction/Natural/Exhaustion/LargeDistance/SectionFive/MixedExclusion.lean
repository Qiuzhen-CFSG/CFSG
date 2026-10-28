module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedGeneratedPath
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedEscape

/-!
# Excluding large distance for the mixed-plane replacement

On a generated mixed-plane critical path the full endpoint radius has
index greater than four at the starting core, while its image at the
first interior core has order two. The exact kernel tower therefore gives
image order greater than two for the full intermediate kernel. The next
backward critical line centralizes this kernel. The three-pair fixed-vector
calculation puts that line in the old first edge seed, while quadratic
critical action puts it in the new first edge seed. These edge kernels
generate the shared stabilizer, which consequently centralizes the line.

The backward construction is refined to retain the original relative
normalizer actor and its agreement with the edge holomorph on the entire
edge kernel. Both geometric transporters remain distinct. For a line fixed
by the shared stabilizer, this agreement makes both transporters preserve
the line. Transport then places the second shifted line in the earlier
starting seed, noncentrally at its stabilizer. Above distance six, the
first path's large kernel fixes this line and places it in the first edge
seed. At distance six the reversed critical path gives that containment
directly. The two selected edge kernels now force contradictory centrality.

Thus the mixed-plane branch has no distance greater than four. The literal
original-radical consumer combines this with the existing pair-plane and
nonsylow exclusions: every remaining replacement above distance four has
an ORIGINAL Sylow radical, restriction index one or two, and replacement
image order sixteen or eight respectively. Larger original-Sylow branches,
distance four, LargeDistanceInput and unconditional replacement distance
two remain open. No original-radical Sylow property is imposed on the
replacement. Both moved-cover orders, all central attachments, the actual
natural graph and the literal quotient maps are preserved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.11), printed pp.915--924, especially the kernel tower,
intermediate-line transport and terminal comparison of (5.11). The private
MixedEscape import reuses the earlier trapped-orbit bound in the refined
holomorph construction, without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedExclusion
local notation "S" => Equiv.Perm (Fin 6)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The full endpoint radius has a kernel of image order greater than two
at the starting vertex of every generated mixed-plane critical path. -/
theorem mixed_radius_kernel_gt_two_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    2 < (Q d.radical a).relIndex
      (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let rev : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hi := (MixedRadius.mixed_opposite_radius_line_knownSimple hb u him rev).1
  change (Q d.radical (p.walk.reverse.getVert (p.walk.reverse.length-2))).relIndex
    (V d.radical a')=2 at hi
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show p.walk.length-(p.walk.length-2)=2 by omega] at hi
  have hk := MixedGeneratedPath.mixed_radius_kernel_le_interior_knownSimple hb u him p hgen
  have he : V d.radical a' ⊓ (Q d.radical a ⊓ Q d.radical (p.walk.getVert 2)) =
      V d.radical a' ⊓ Q d.radical a :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
      (le_inf inf_le_left (le_inf inf_le_right hk))
  have he' := congrArg (fun N : Subgroup (FreeAmalgam d.radical) => N.relIndex (V d.radical a')) he
  simp only [inf_relIndex_left] at he'
  have ht := relIndex_inf_mul_relIndex (Q d.radical a)
    (Q d.radical (p.walk.getVert 2)) (V d.radical a')
  rw [he',hi,inf_comm (Q d.radical (p.walk.getVert 2))] at ht
  have hlarge := MixedGeneratedPath.mixed_generated_radius_gt_four_knownSimple hb u him p hgen
  omega

/-- The large full-radius kernel centralizes the next critical line.
The two incident kernels selected at the shared vertex then fix that line. -/
theorem mixed_next_line_central_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hover : ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i)
    (hqgen : Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (q.walk.getVert 3) =
      stabilizer d.radical (q.walk.getVert 2)) :
    ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  let c := p.walk.getVert (p.walk.length-2)
  let H := ⁅Z d.radical z,Z d.radical c⁆
  let A := V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hql : q.walk.length = replacementDistance h d := q.length_eq_b
  have hq2 : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by omega)
  have hnear : (cosetGraph d.radical).dist z a ≤ 2 := by
    rw [←hq2,q.dist_start (by omega)]
  have hHZ : H ≤ Z d.radical a := by
    rw [show H = ⁅Z d.radical z,Z d.radical c⁆ from rfl,
      ←MixedRadius.mixed_near_seed_radius_commutator_knownSimple hb u him p q hnear]
    exact (MixedRadius.mixed_opposite_radius_line_knownSimple hb u him p).2.2.1.trans inf_le_left
  have hHc : H ≤ Z d.radical c :=
    ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hcV : V d.radical a' ≤ Q d.radical c := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-(p.walk.length-2)+2 < replacementDistance h d
    omega
  have hHA : H ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (hHc.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.end_color))).trans
        (centralizer_le (inf_le_left.trans hcV))
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have h₂₁ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hA : A ≤ Q d.radical (p.walk.getVert 1) :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht h₂₁)
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) :=
    (le_inf hHZ hHA).trans (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA
      (mixed_radius_kernel_gt_two_knownSimple hb u him p hgen))
  have hback : H ≤ Z d.radical (q.walk.getVert 1) :=
    cube_critical_commutator_le_first_seed s hc u hR q
  have hqt : color d.radical (q.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 0) (by omega)))
    rw [SimpleGraph.Walk.getVert_zero,q.start_color] at hh
    cases he : color d.radical (q.walk.getVert 1) <;> simp_all
  have hseed (v : Vertex d.radical) (hv : color d.radical v=true) :
      Z d.radical v ≤ centralizer (Q d.radical v : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [hv])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mp
  have hgg : Q d.radical (q.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 1) =
      stabilizer d.radical a := by simpa only [hq2,hq3] using hqgen
  rw [←hgg]
  exact sup_le (le_centralizer_iff.mp (hback.trans (hseed _ hqt)))
    (le_centralizer_iff.mp (hfirst.trans (hseed _ ht)))

private theorem relative_shift_with_agreement
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical k c)
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k c)) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ g ∈ stabilizer d.radical (alpha d.radical),
          ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v := by
  have hex : ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical),
      ¬ (Z d.radical c).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    by_contra! hall
    have htrap : conjugateSpanBy (Z d.radical c)
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact iSup_le (fun g => hall g g.property)
    exact (not_lt_of_ge (MixedEscape.trapped_slice_bound s hc hb u him p hp htrap hat hct hgen)) hindex
  obtain ⟨g,hg,hout⟩ := hex
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical c ≤ Q d.radical t :=
    ((Z_le_VBall d.radical c 2).trans ((replacementGeometry h d).V_le_Q hb c hcol)).trans
      (Q_le_adjacent_h d.radical ht hct)
  obtain ⟨j,hj,he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t c hcol hct g hg.1
  have hZ : Z d.radical (act d.radical j⁻¹ c) =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZt he
  have hU : U d.radical (act d.radical j⁻¹ c) =
      (U d.radical c).map (MulAut.conj g).toMonoidHom := by
    rw [U_act,inv_inv]
    exact Escape.Propagation.Backward.Products.map_conj_eq_of_agree
      ((DistanceEight.U_le_Z d.radical c).trans hZt) he
  have hct' : Adjacent d.radical (act d.radical j⁻¹ c) t := by
    have hfix : act d.radical j⁻¹ t = t := (stabilizer d.radical t).inv_mem hj
    simpa only [hfix] using (adjacent_act_iff d.radical j⁻¹ c t).mpr hct
  let w : (cosetGraph d.radical).Walk (act d.radical j⁻¹ c) (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct')
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hbad : ¬ Z d.radical (act d.radical j⁻¹ c) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2)) := by rwa [hZ]
  have hcolor : color d.radical (act d.radical j⁻¹ c) = false := by
    rw [action_preserves_color,hcol]
  let q := p.prepend_two (Nat.le_of_lt hb) hcolor w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨j⁻¹,(stabilizer d.radical t).inv_mem hj,q,hqt,
    fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_,g,hg.2,?_⟩
  swap
  · simpa only [inv_inv] using he
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hg.2)
  rw [hU,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hB]


/-- A selected path retains both geometric transporters and the original
local actor whose action the edge holomorph realizes. -/
private structure GeneratedShift {a a' : Vertex d.radical}
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

private theorem generated_shift_base
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    Nonempty (GeneratedShift (h := h) p) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hb2 : 2 < replacementDistance h d := by omega
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hpair,hgen⟩ := MixedGeneratedPath.mixed_aligned_generating_neighbor_knownSimple hb u him p
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
  have hstrict := MixedLarge.mixed_forward_slice_strict_knownSimple hb u him p
  obtain ⟨k,hk,q,hq1,hover,hidx,g,hg,hagree⟩ := relative_shift_with_agreement s hc hb2 u hf p
    (by rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him p).1]; decide)
    hat hct hgen (by rwa [hi])
  exact ⟨⟨_,t,x,hx,hxt,k,hk,rfl,g,hg,hagree,hat,q,hq1,hover,(sup_comm _ _).trans hpair⟩⟩

private theorem GeneratedShift.interior_generation {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : GeneratedShift (h := h) p) (hb : 2 < replacementDistance h d) :
    Q d.radical (q.path.walk.getVert 1) ⊔ Q d.radical (q.path.walk.getVert 3) =
      stabilizer d.radical (q.path.walk.getVert 2) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have he : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  rw [q.first,q.overlap 1 (by omega),he]
  exact q.generation

private theorem GeneratedShift.conjugate {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : GeneratedShift (h := h) p) (j : FreeAmalgam d.radical) :
    Nonempty (GeneratedShift (h := h) (p.act j)) := by
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
    (adjacent_act_iff d.radical j _ _).mpr q.adjacent_start,w,hw1,hwo,?_⟩⟩
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

private theorem generated_shift_of_vertices
    {a a' c c' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c c')
    (ha : c=a) (he : c'=a') (hv : ∀ i, q.walk.getVert i=p.walk.getVert i)
    (hr : Nonempty (GeneratedShift (h := h) q)) : Nonempty (GeneratedShift (h := h) p) := by
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
    r.agreement,r.adjacent_start,w,hw1,hwo,by simpa only [hv] using r.generation⟩⟩

private theorem generated_shift_at
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Nonempty (GeneratedShift (h := h) p) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := generated_shift_base hb u him (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act g⁻¹)
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact generated_shift_of_vertices p ((p.act g⁻¹).act g)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate g)

omit [Finite G] in
private theorem seed_centralizes_edge {t : Vertex d.radical}
    (ht : color d.radical t=true) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  intro x hx
  rw [Z,if_neg (by simp [ht])] at hx
  exact (mem_omegaCenter_iff.mp hx).2.2

private theorem GeneratedShift.adjacent_shift {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : GeneratedShift (h := h) p) : Adjacent d.radical q.start q.edge := by
  have hl : 0 < q.path.walk.length := q.path.length_eq_b ▸ replacementDistance_pos h d
  have hh := q.path.walk.adj_getVert_succ (i := 0) hl
  rw [SimpleGraph.Walk.getVert_zero,q.first] at hh
  exact (cosetGraph_adj d.radical _ _).mp hh

private theorem GeneratedShift.edge_color {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'}
    (q : GeneratedShift (h := h) p) : color d.radical q.edge=true := by
  have hh := adjacent_color_ne d.radical q.adjacent_start
  rw [p.start_color] at hh
  cases he : color d.radical q.edge <;> simp_all

private theorem central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

private theorem central_line_le_neighbor {c v w : Vertex d.radical}
    (hv : Adjacent d.radical c v) (hw : Adjacent d.radical c w)
    (H : Subgroup (FreeAmalgam d.radical))
    (hH : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)))
    (hHv : H ≤ Z d.radical v) : H ≤ Z d.radical w := by
  obtain ⟨g,hg,hgw⟩ := stabilizer_transitive_neighbors d.radical c hv hw
  rw [←hgw,Z_act,←central_fixed_map H (stabilizer d.radical c) hH
    ((stabilizer d.radical c).inv_mem hg)]
  exact map_mono hHv

/-- Holomorph agreement, rather than an identification of stabilizers,
transports the fixed critical line back through both selected actors. -/
private theorem generated_central_transport
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : GeneratedShift (h := h) p)
    (hcentral : ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    H ≤ Z d.radical (p.walk.getVert 2) ∧
      ¬ H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hHedge : H ≤ Z d.radical q.edge := by
    simpa only [q.first] using cube_critical_commutator_le_first_seed s hc u hR q.path
  have hHQ : H ≤ Q d.radical q.edge := by
    intro x hx
    have hh := hHedge hx
    rw [Z,if_neg (by simp [q.edge_color])] at hh
    exact (mem_omegaCenter_iff.mp hh).1
  have hk : H.map (MulAut.conj q.edgeActor⁻¹).toMonoidHom = H :=
    (Escape.Propagation.Backward.Products.map_conj_eq_of_agree hHQ q.agreement).trans
      (central_fixed_map H (stabilizer d.radical a) hcentral q.original_mem)
  have hx : H.map (MulAut.conj q.localActor⁻¹).toMonoidHom = H :=
    central_fixed_map H (stabilizer d.radical a) hcentral
      ((stabilizer d.radical a).inv_mem q.local_mem)
  have hHstart : H ≤ Z d.radical q.start :=
    ((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hHZ : H ≤ Z d.radical (p.walk.getVert 2) := by
    rw [←q.start_eq,Z_act,←hk] at hHstart
    have hh := (map_le_map_iff_of_injective (MulAut.conj q.edgeActor⁻¹).injective).mp hHstart
    rw [Z_act,←hx] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj q.localActor⁻¹).injective).mp hh
  refine ⟨hHZ,?_⟩
  intro hcentral₂
  apply critical_commutator_not_central s hc q.path
  have hh := (map_mono (f := (MulAut.conj q.localActor⁻¹).toMonoidHom) hcentral₂).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj q.localActor⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (p.walk.getVert 2)).map
      (MulAut.conj q.localActor⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rw [hx,←stabilizer_act] at hh
  have hh' := (map_mono (f := (MulAut.conj q.edgeActor⁻¹).toMonoidHom) hh).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj q.edgeActor⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (act d.radical q.localActor (p.walk.getVert 2))).map
      (MulAut.conj q.edgeActor⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh'
  rwa [hk,←stabilizer_act,q.start_eq] at hh'

/-- The mixed-plane large-radius branch is impossible on the actual
minimum characteristic replacement. The proof retains both holomorph
transporters and their agreement on the full edge kernel. -/
theorem mixed_four_lt_false_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom) : False := by
  obtain ⟨a₀',⟨p₀⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  obtain ⟨v⟩ := generated_shift_at hb u him p₀
  obtain ⟨q⟩ := generated_shift_at hb u him v.path
  obtain ⟨r⟩ := generated_shift_at hb u him q.path
  let p := v.path
  let a := v.start
  let a' := p₀.walk.getVert (p₀.walk.length-2)
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let H := ⁅Z d.radical r.start,Z d.radical z₄⁆
  have hlp : p.walk.length=replacementDistance h d := p.length_eq_b
  have hlq : q.path.walk.length=replacementDistance h d := q.path.length_eq_b
  have hlr : r.path.walk.length=replacementDistance h d := r.path.length_eq_b
  have hq2 : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hcentral : H ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) :=
    mixed_next_line_central_knownSimple hb u him q.path (q.interior_generation (by omega))
      r.path r.overlap (r.interior_generation (by omega))
  have htransfer := generated_central_transport hb u him q.path r hcentral
  change H ≤ Z d.radical (q.path.walk.getVert 2) ∧
    ¬ H ≤ centralizer (stabilizer d.radical (q.path.walk.getVert 2) : Set (FreeAmalgam d.radical)) at htransfer
  rw [hq2] at htransfer
  obtain ⟨hHZ,hnon⟩ := htransfer
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hHback : H ≤ Z d.radical r.edge := by
    simpa only [r.first] using cube_critical_commutator_le_first_seed s hc u hR r.path
  have hHedge : H ≤ Z d.radical q.edge :=
    central_line_le_neighbor r.adjacent_start q.adjacent_shift H hcentral hHback
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) := by
    by_cases hb6 : 6 < replacementDistance h d
    · let A := V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)
      have hHe : H ≤ Z d.radical z₄ :=
        ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
          (DistanceEight.U_le_Z d.radical _)
      have hd₂ : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) z₄ = 2 := by
        rw [SimpleGraph.dist_comm]
        change (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) _ = 2
        rw [q.path.dist_end]
        omega
      have hd₀ : (cosetGraph d.radical).dist a' (p.walk.getVert (p.walk.length-2)) = 2 := by
        rw [SimpleGraph.dist_comm,p.dist_end]
        omega
      have hd : (cosetGraph d.radical).dist a' z₄ ≤ 4 := by
        have hh := (cosetGraph_connected d.radical).dist_triangle (u := a')
          (v := p.walk.getVert (p.walk.length-2)) (w := z₄)
        omega
      have hVA : V d.radical a' ≤ Q d.radical z₄ := by
        apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
        change (cosetGraph d.radical).dist a' z₄+2 < replacementDistance h d
        omega
      have hHA : H ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
        (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical z₄ r.path.end_color))).trans
            (centralizer_le (inf_le_left.trans hVA))
      have h₂₁ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
        adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
          (p.walk.adj_getVert_succ (i := 1) (by omega)))
      have hA : A ≤ Q d.radical (p.walk.getVert 1) :=
        inf_le_right.trans (Q_le_adjacent_h d.radical ht h₂₁)
      exact (le_inf hHZ hHA).trans (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA
        (mixed_radius_kernel_gt_two_knownSimple hb u him p (v.interior_generation (by omega))))
    · have heven := replacementDistance_even h d
      rw [Nat.even_iff] at heven
      have heq : replacementDistance h d=6 := by omega
      let rev : CriticalPath d.radical (replacementGeometry h d) z₄ r.start :=
        ⟨r.path.end_color,r.path.walk.reverse,
          by rw [SimpleGraph.Walk.length_reverse,r.path.shortest,SimpleGraph.dist_comm],
          critical_reverse_pair s hc r.path⟩
      have hh := cube_critical_commutator_le_first_seed s hc u hR rev
      change ⁅Z d.radical z₄,Z d.radical r.start⁆ ≤ Z d.radical (r.path.walk.reverse.getVert 1) at hh
      rw [commutator_comm,SimpleGraph.Walk.getVert_reverse] at hh
      have he : r.path.walk.getVert (r.path.walk.length-1)=p.walk.getVert 1 := by
        rw [hlr,heq,show 6-1=3+2 from rfl,r.overlap 3 (by omega),
          show 3=1+2 from rfl,q.overlap 1 (by change 1 ≤ p.walk.length-2; omega)]
      rwa [he] at hh
  apply hnon
  apply le_centralizer_iff.mp
  rw [←q.generation]
  exact sup_le (le_centralizer_iff.mp (hHedge.trans (seed_centralizes_edge q.edge_color)))
    (le_centralizer_iff.mp (hfirst.trans (seed_centralizes_edge ht)))


/-- Every order-four replacement image has distance at most four: its
pair-plane alternative already has distance two, and its mixed alternative
is excluded above four by the actual generated-path argument. -/
theorem four_image_distance_le_four_knownSimple
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    replacementDistance h d ≤ 4 := by
  by_contra! hb
  obtain ⟨u,him⟩ := PairExclusion.four_image_mixed_knownSimple (by omega) hfour
  exact mixed_four_lt_false_knownSimple hb u him

include e hz hn in
/-- The literal original MS radical must be Sylow above distance four.
Its restriction contains the replacement with index one or two, and the
actual replacement image has order sixteen or eight respectively. -/
theorem four_lt_original_sylow_large_image_knownSimple
    (hb : 4 < replacementDistance h d) :
    (∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      ((d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 1 ∧
        Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) ∨
       (d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 2 ∧
        Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)) := by
  have hs : ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R) := by
    by_contra hns
    exact (Nat.not_le_of_gt hb)
      (nonsylow_replacementDistance_le_four_knownSimple (e := e) (hz := hz) (hn := hn) hns)
  obtain ⟨P,hP⟩ := hs
  have hdata := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) P hP
  have hprod := hdata.2.2.1
  refine ⟨⟨P,hP⟩,?_⟩
  rcases hdata.2.2.2 with hi | hi | hi
  · exact Or.inl ⟨hi,by rw [hi,Nat.mul_one] at hprod; exact hprod⟩
  · exact Or.inr ⟨hi,by rw [hi] at hprod; omega⟩
  · have hf : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d))=4 := by
      rw [hi] at hprod
      omega
    exact False.elim ((Nat.not_le_of_gt hb) (four_image_distance_le_four_knownSimple hf))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedExclusion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
