module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EndpointSpan
public import Theory.ThreeSubgroups

/-!
# Predecessor slices and the whole residual core

A small predecessor Baumann slice identifies the full reverse critical
kernel on an arbitrary distance-four path. Its commutator with the midpoint
two-core has order at most two and is fixed by the whole midpoint stabilizer;
no conjugacy of the two endpoints in that stabilizer is required. The
three-subgroups lemma then makes the whole midpoint residual core fix that
kernel. The full-cover pointwise-fixer theorem puts its endpoint action in
the critical line and bounds its actual endpoint quotient image by two.

Apply this to the reverse of the reciprocal critical path furnished by a
nonabelian selected span. A small forward slice now bounds the image of the
whole starting residual core in the midpoint quotient. This discharges the
core-index premise in the existing source supplement argument.

Forward escape also forces the selected residual-moved span to be moved by
the critical endpoint modulo the starting seed, without assuming that the
selected span is nonabelian. Consequently the literal whole-core endpoint
estimate supplies nonabelianness. Under full point-core equality and a small
forward slice, that same endpoint estimate gives the actual whole-core
supplement, equality of its derived subgroup with the selected derived
subgroup, the derived order bound at every original vertex, and the common
kernel's commutator bound at the starting vertex. The whole-core bound uses
the proved supplement; it is not inferred from a selected-span bound alone.

The whole-core endpoint estimate remains explicit in the final application.
The general selected endpoint estimate, unconditional opposite-core action,
other radical images and both final distance conclusions remain unproved.
Both central covers, the original graph and its quotient maps are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10), (5.8) and the selected-core argument in (5.12), printed
pp.879--881,919--920,924--927. The first proof extends the existing
BackwardFixedCore midpoint calculation using PredecessorSlice's actual
kernel equality; the movement proof extends SelectedCoreMovement using
forward escape in place of its nonabelianness premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- A small predecessor slice fixes its reverse-kernel/core commutator
at the midpoint, without an endpoint-conjugacy assumption. -/
theorem predecessor_slice_kernel_core_commutator
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let K := Z d.radical a' ⊓ Q d.radical a
    let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
    Nat.card H ≤ 2 ∧ H ≤ Z d.radical (p.walk.getVert 3) ∧
      H ≤ fixedCore d.radical (p.walk.getVert 2) ∧
      H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let K := Z d.radical a' ⊓ Q d.radical a
  let H := ⁅K,Q d.radical c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases hx : color d.radical t <;> simp_all
  have hslice := critical_predecessor_slice_eq_kernel s hc hb2 p (by
    simpa only [hl,Nat.reduceSub] using hindex)
  have hKslice' := hslice.1
  simp only [hl,Nat.reduceSub] at hKslice'
  have hKslice : K = Z d.radical a' ⊓ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hKslice'.symm
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hKslice ▸ inf_le_right
  have hAn : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    rw [hKslice]
    exact (le_inf
      ((show Q d.radical t ≤ stabilizer d.radical a' from
        fun _ hx => hx.2 _ (adjacent_symm d.radical het)).trans (Z_normalized d.radical a'))
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans
        (Escape.Propagation.Rigidity.B_normalized hb2 c hcol))).trans inf_normalizer_le_normalizer_inf
  have hcard : Nat.card H ≤ 2 := by
    have hh := small_critical_kernel_predecessor_card s hc hb2 u hR p (by
      rw [hslice.2.1]; decide)
    simpa only [hl,Nat.reduceSub] using hh
  have hfixed : H ≤ fixedCore d.radical c :=
    small_slice_core_commutator_le_fixedCore (h := h) hb2 hcol K hKB hcard
  have hcentral : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) :=
    small_slice_edge_core_commutator_central (h := h) hb2 hcol hct K hKB hAn hcard
  have hHK : H ≤ K := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_adjacent_h d.radical ht hct).trans hAn)
  have hHQt : H ≤ Q d.radical t := (hfixed.trans inf_le_left).trans
    (Q_le_adjacent_h d.radical ht hct)
  have hHt : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    hcentral.trans (centralizer_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hct)))
  have hseed : H ≤ Z d.radical t := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hHQt hx,
      elemPow_eq_one_of_isElementaryAbelian x (show x ∈ Z d.radical a' from (hHK hx).1),hHt hx⟩
  exact ⟨hcard,hseed,hfixed,hcentral⟩


include s in
/-- A small predecessor slice makes the whole midpoint residual core fix
the reverse critical kernel. Its endpoint image has order at most two. -/
theorem predecessor_slice_residual_core_endpoint
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let C := ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆
    C ≤ centralizer (Z d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅C,Z d.radical a'⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ ∧
      (Q d.radical a').relIndex C ≤ 2 := by
  let c := p.walk.getVert 2
  let K := Z d.radical a' ⊓ Q d.radical a
  let C := ⁅Q d.radical c,Ltilde d.radical c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hslice := critical_predecessor_slice_eq_kernel s hc hb2 p (by
    simpa only [hl,Nat.reduceSub] using hindex)
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) := by
    have he := hslice.1
    simp only [hl,Nat.reduceSub] at he
    exact he.ge.trans inf_le_right
  have hLK : ⁅Ltilde d.radical c,K⁆ ≤ Z d.radical c := by
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff d.radical c _
      ((replacementGeometry h d).V_le_Q hb2 c hcol |>.trans (fun _ hx => hx.1)) k).mp
        (hKB hk)).2 l hl
  have hfixed := (predecessor_slice_kernel_core_commutator s hc hb u hR p hindex).2.2.2
  have hCK : C ≤ centralizer (K : Set (FreeAmalgam d.radical)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · exact le_bot_iff.mp ((commutator_mono hLK le_rfl).trans_eq
        (Z_centralizes_Q d.radical c hcol))
    · exact commutator_eq_bot_iff_le_centralizer.mpr
        (hfixed.trans (centralizer_le (Ltilde_le_stabilizer _)))
  have hCQ : C ≤ Q d.radical c := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))
  have hct : Adjacent d.radical c (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent d.radical a' (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases hx : color d.radical (p.walk.getVert 3) <;> simp_all
  have hCG : C ≤ stabilizer d.radical a' :=
    (hCQ.trans (Q_le_adjacent_h d.radical ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical het))
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    rw [hslice.2.1]; decide
  have hcomm := small_critical_kernel_commutator s hc p hsmall C hCG hCK
  let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color
    (critical_reverse_pair s hc p)
  have hbound : C ≤ Q d.radical a' ⊔ Z d.radical a :=
    (le_inf hCG hCK).trans (small_critical_kernel_centralizer s hc q (by
      rw [hslice.2.2]; decide))
  let J := Q d.radical a' ⊔ Z d.radical a
  have hZa : Z d.radical a ≤ stabilizer d.radical a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hJG : J ≤ stabilizer d.radical a' := sup_le (fun _ hx => hx.1) hZa
  let := finite_stabilizer d.radical a'
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let : ((Q d.radical a').subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (hJG.trans (Q_normalized d.radical a'))
  have hi := relIndex_sup_left ((Z d.radical a).subgroupOf J) ((Q d.radical a').subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  have hCindex : (Q d.radical a').relIndex C ≤ 2 := by
    calc
      _ ≤ (Q d.radical a').relIndex J := relIndex_le_of_le_right hbound index_ne_zero_of_finite
      _ = (Q d.radical a').relIndex (Z d.radical a) := hi
      _ = 2 := hslice.2.1
  exact ⟨hCK,hcomm,hCindex⟩

/-- A nonabelian selected span and its small forward slice bound the image
of the whole starting residual core in the actual midpoint quotient. -/
theorem selected_whole_core_index_of_small_slice_knownSimple
    (hb : 2 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨hfour,x,hx,q,hq1,hq2,hq3⟩ :=
    selected_span_conjugate_critical_path (h := h) hb p hnonabelian
  let r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical x (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hr2 : r.walk.getVert 2 = alpha d.radical := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length = 4 from q.length_eq_b.trans hfour]
    exact hq2
  have hh := (predecessor_slice_residual_core_endpoint s hc hfour u hf r (by
    simpa only [hr2] using hslice)).2.2
  simpa only [hr2] using hh


include h in
private theorem core_endpoint_span_le_core
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
  apply (localZSpan_le_V d.radical _).trans
    (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]


omit [Finite G] in
private theorem core_endpoint_comap_normal (J : Subgroup (FreeAmalgam d.radical))
    (hJ : stabilizer d.radical (alpha d.radical)≤normalizer (J:Set (FreeAmalgam d.radical))) :
    (J.comap (embedM d.radical)).Normal := by
  constructor
  intro n hn g
  change embedM d.radical (g*n*g⁻¹)∈J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM d.radical g)
    (by change embedM d.radical g∈stabilizer d.radical (mVertex d.radical 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn



include s in
/-- Forward escape makes the selected residual-moved span nontrivial modulo
the starting seed, hence the critical endpoint moves it. This does not
assume that the selected span is nonabelian. -/
theorem selected_moved_span_endpoint_movement_of_escape
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d)) :
    ¬ ⁅forwardMovedSpan d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤
      Z d.radical (alpha d.radical) := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let W := forwardMovedSpan d.radical c
  let f := embedM d.radical
  let Pm := P.comap f
  let Wm := W.comap f
  let Zm := (Z d.radical (alpha d.radical)).comap f
  let Am := (Z d.radical a').comap f
  let K := replacementComponent d
  have hGa : stabilizer d.radical (alpha d.radical) = f.range := stabilizer_m_base d.radical
  have hPQ : P ≤ Q d.radical (alpha d.radical) := core_endpoint_span_le_core hb p
  have hPG : P ≤ f.range := (hPQ.trans (fun _ hx => hx.1)).trans_eq hGa
  have hPm : Pm.map f = P := map_comap_eq_self hPG
  have hWm : Wm.map f = W := map_comap_eq_self ((forwardMovedSpan_le d.radical c).trans hPG)
  have hZm : Zm.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq hGa)
  have hAm : Am.map f = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq hGa)
  have hKm : K.map f = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  let : Pm.Normal := core_endpoint_comap_normal _ (localZSpan_normalized d.radical _ _)
  let : Wm.Normal := core_endpoint_comap_normal _ (forwardMovedSpan_normalized d.radical _)
  let : Zm.Normal := core_endpoint_comap_normal _ (Z_normalized d.radical _)
  have hPcore : Pm ≤ pCore 2 d.overgroup := by
    have hh := comap_mono (f := f) hPQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hWP : Wm = ⁅Pm,K⁆ := by
    apply map_injective (embedM_injective d.radical)
    rw [map_commutator,hWm,hPm,hKm]
    rfl
  have hKperfect : IsPPerfect 2 K := by
    rw [show K = pResidual 2 d.overgroup from (replacement_residual h d).symm]
    exact isPPerfect_pResidual 2
  have hidem : ⁅Wm,K⁆ = Wm := by
    rw [hWP]
    exact commutator_isPPerfect_idempotent K Pm hKperfect
      (pCore_isPGroup.to_le hPcore) le_normalizer_of_normal
  have hA : ¬ Am ≤ pCore 2 d.overgroup := by
    intro ha
    apply (critical_reverse_pair s hc p).2
    have hh := map_mono (f := f) ha
    rwa [hAm,←Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  intro hcomm
  have hcommm : ⁅Wm,Am⁆ ≤ Zm := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hWm,hAm]
    exact hcomm
  have hfixed := component_commutator_le_of_section_fixed s Wm Zm Am hcommm hA
  change ⁅Wm,K⁆ ≤ Zm at hfixed
  rw [hidem] at hfixed
  have hh := map_mono (f := f) hfixed
  rw [hWm,hZm] at hh
  apply critical_forward_not_le_slice_of_escape s hc hb hesc p
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  intro z hz
  have hzP : z ∈ P := (Z_le_localZSpan d.radical _ _)
    (DistanceEight.U_le_Z d.radical _ hz)
  apply (mem_B_iff d.radical (alpha d.radical) _
    ((replacementGeometry h d).V_local _ rfl hb) z).mpr
  refine ⟨hPV hzP,?_⟩
  intro l hl
  apply hh
  change ⁅l,z⁆ ∈ ⁅P,Ltilde d.radical (alpha d.radical)⁆
  rw [commutator_comm]
  exact commutator_mem_commutator hl hzP

/-- The literal whole-core endpoint estimate forces the selected span to
be nonabelian in the full-point branch. An abelian span would put its entire
residual-moved subgroup inside the midpoint core, contradicting escape. -/
theorem full_point_selected_span_nonabelian_of_core_endpoint_knownSimple
    (hb : 2 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hesc := full_point_criticalEscape s hc hb u hf
  intro he
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases hh' : color d.radical t <;> simp_all
  have hPG : P ≤ stabilizer d.radical c :=
    (((selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left).trans
      (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hPQ : P ≤ Q d.radical c := by
    rw [←C_eq_Q s hc c hcol]
    exact le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (centralizer_le (Z_le_localZSpan d.radical c (alpha d.radical))))
  have hWC : forwardMovedSpan d.radical c ≤
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ :=
    commutator_mono (core_endpoint_span_le_core hb p) le_rfl
  have hWQ : forwardMovedSpan d.radical c ≤ Q d.radical c :=
    (forwardMovedSpan_le d.radical c).trans hPQ
  exact selected_moved_span_endpoint_movement_of_escape s hc hb p hesc
    ((commutator_mono (le_inf hWC hWQ) le_rfl).trans hactor)


/-- The small forward slice discharges the whole-core index in the source
supplement argument. The remaining core/endpoint commutator is stated
literally. The derived bound is on the whole residual core at every original
vertex, obtained through its proved supplement by the selected moved span. -/
theorem full_point_four_whole_core_bounds_of_small_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    C ≤ Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) ∧
      ⁅C,C⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ∧
      (∀ v : Vertex d.radical, color d.radical v = false →
        Nat.card (⁅⁅Q d.radical v,Ltilde d.radical v⁆,⁅Q d.radical v,Ltilde d.radical v⁆⁆ :
          Subgroup (FreeAmalgam d.radical)) ≤ 2) ∧
      ⁅Q d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hnonabelian := full_point_selected_span_nonabelian_of_core_endpoint_knownSimple
    hb2 u hfull p hactor
  have hindex := selected_whole_core_index_of_small_slice_knownSimple hb2 u hfull.le p hslice hnonabelian
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hd := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
  have hfixed := hd.2.trans (centralizer_le (Ltilde_le_stabilizer _))
  have hs := selected_core_supplement_knownSimple_of_nonabelian
    (e := e) (hz := hz) (hn := hn) hb2 p (by omega) hnonabelian hindex hactor
  have hderived := hs.2.trans (selected_span_derived_eq_moved hb2 p hfixed).symm
  have hcard : Nat.card (⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆,
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    rw [hderived]
    exact hd.1
  refine ⟨hs.1,hderived,?_,selected_core_cross_commutator_of_supplement hb2 p hfixed hs.1⟩
  intro v hv
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hv
  have he : act d.radical g (alpha d.radical) = v := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  rw [←he,Q_act,Ltilde_act,←map_commutator,←map_commutator,
    card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact hcard


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
