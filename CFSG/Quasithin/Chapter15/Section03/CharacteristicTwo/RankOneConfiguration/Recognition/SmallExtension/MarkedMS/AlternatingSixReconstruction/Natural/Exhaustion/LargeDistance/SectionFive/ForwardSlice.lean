module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# Eligible edge slices and the nonzero forward line

Every oriented source edge has a neighboring moved cover outside the
starting Baumann subgroup. Otherwise the normal span of that edge radius
would place the entire radius in the Baumann subgroup, contradicting its
proved nontrivial component action modulo the seed. The replacement
application constructs an actual shortest two-edge segment through the
original first edge, with moving-layer slice index at least two.

For a small critical image, the full forward-kernel commutator vanishes
exactly when the second moving cover lies in the starting Baumann subgroup.
If it vanished, normal generation would make the selected span centralize
both inner layers. The full reverse critical kernel then bounds its endpoint
commutator by the starting seed, and residual action places the span in the
Baumann subgroup. This retains both central covers and the literal kernels.

An eligible forward slice of index at most two consequently gives a line
of order two, central at the starting vertex and noncentral at the second
vertex. The known-simple application no longer needs nonabelianness of the
selected span for this step. The selected segment still needs to be extended
to the prescribed backward critical path; the opposite slice, exact-four
radius exclusion, intermediate R4/R6 and both terminal contradictions remain
with qt-e-ms-small-a6-exhaustion-large-distance. These forward-line statements
do not identify R4 or R6. Final whole-core reconstruction remains with
qt-e-ms-small-a6-reconstruction.

Source: Meierfrankenfeld--Stellmacher (1993), the eligible-neighbor selection
in (5.8), pp.919--920, and the nonzero forward-line step in (5.9), pp.920--922.
The edge-radius selection and normal-span proof adapt
SymplecticSetup.BackwardEscape and ForwardKernelNonzeroAll to the full
central covers, using SmallKernel and ForwardClosure in place of the native
full-point and natural-subgroup hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem radius_le_predecessor_stabilizer (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    V d.radical (alpha d.radical) ≤ stabilizer d.radical (p.walk.getVert (p.walk.length-2)) := by
  apply (V_le_iff d.radical rfl _).mpr
  intro v hd hdist
  apply Z_le_stabilizer_of_dist_le v ((replacementGeometry h d).exists_critical v hd)
  rw [(replacementGeometry h d).distance_constant v hd]
  change (cosetGraph d.radical).dist v (p.walk.getVert (p.walk.length-2)) ≤ replacementDistance h d
  have ht := (cosetGraph_connected d.radical).dist_triangle (u:=v) (v:=alpha d.radical)
    (w:=p.walk.getVert (p.walk.length-2))
  rw [p.dist_start (Nat.sub_le _ _)] at ht
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  omega


include s in
/-- Every source edge admits a neighboring moved cover outside the Baumann slice.
The whole radius cannot be fixed modulo its seed, and normal generation of
one edge radius reduces that noncontainment to a single neighbor. -/
theorem exists_eligible_neighbor_at_edge
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ c, Adjacent d.radical c t ∧
      ¬ U d.radical c ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hVB : ¬ V d.radical a ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
    intro hVB
    apply radius_moving_not_le_Z s hc hb a ha
    change ⁅V d.radical a,Ltilde d.radical a⁆ ≤ Z d.radical a
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    exact ((mem_B_iff d.radical a _
      ((replacementGeometry h d).V_local a ha (by
        rw [(replacementGeometry h d).distance_constant a ha]; exact hb)) v).mp (hVB hv)).2 l hl
  by_contra! hn
  apply hVB
  apply radius_le_of_normalized_edge ha hat _ _
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
  apply CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion.radius_le_of_h_neighbors ha hat
  intro c hct
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases he : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
  exact sup_le (hn c hct)
    ((adjacent_Z_le d.radical ha hat).trans (Escape.EdgeTransfer.Z_le_B hb a ha))

include s in
/-- In the small critical branch the full forward kernel fixes the moving
cover exactly when that cover is in the starting Baumann slice. No
nonabelian orbit-span assumption is used. -/
theorem small_forward_kernel_eq_bot_iff_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ = ⊥ ↔
      U d.radical (p.walk.getVert 2) ≤
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTQt : T ≤ Q d.radical t := inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)
  have hseed : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  constructor
  · intro hzero
    have hZc : Z d.radical c ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
      rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero) hseed
    have hNC : stabilizer d.radical (alpha d.radical) ≤ normalizer
        (centralizer (T : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
      hTN.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
    have hPC : P ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
      dsimp only [P]
      rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      rintro _ ⟨z,hz,rfl⟩
      exact (mem_normalizer_iff.mp
        (hNC ((stabilizer d.radical (alpha d.radical)).inv_mem g.property)) z).mp (hZc hz)
    have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
    have hinner := selected_forward_kernel_contains_inner_layers (h := h) hb p
    have hpre : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
      apply (p.vertex_color (Nat.sub_le _ _)).mpr
      have he := replacementDistance_even h d
      rw [Nat.even_iff] at he ⊢
      have hh : p.walk.length = replacementDistance h d := p.length_eq_b
      omega
    have hPpre : P ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
      rw [←C_eq_Q s hc _ hpre]
      exact le_inf (hPV.trans (radius_le_predecessor_stabilizer (h := h) hb p))
        (hPC.trans (centralizer_le (show Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ T from le_sup_left.trans hinner)))
    have hcomm : ⁅P,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
      small_critical_predecessor_commutator s hc hb p hsmall P hPpre
        (hPC.trans (centralizer_le (show Z d.radical a' ⊓ Q d.radical (alpha d.radical) ≤ T from le_sup_right.trans hinner)))
    exact (DistanceEight.U_le_Z d.radical c).trans ((Z_le_localZSpan d.radical _ _).trans
      (normalized_radius_le_slice_of_critical_commutator s hc hb p P hPV
        (localZSpan_normalized d.radical _ _) hcomm))
  · intro hslice
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    change T ≤ centralizer (U d.radical c : Set (FreeAmalgam d.radical))
    intro x hx y hy
    exact hx.2 y ⟨hy,hslice hy⟩

/-- The literal eligible forward slice supplies a nonzero line, central at
the start and noncentral at the second vertex, even if the selected span
has not yet been shown nonabelian. Both central covers are retained. -/
theorem small_forward_slice_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (heligible : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical (p.walk.getVert 2),T⁆
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) = 2 ∧
      Nat.card H = 2 ∧ H ≤ Z d.radical (p.walk.getVert 1) ∧
      H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTQt : T ≤ Q d.radical t := inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)
  have hTG : T ≤ stabilizer d.radical c :=
    hTQt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHne : H ≠ ⊥ := fun he => heligible
    ((small_forward_kernel_eq_bot_iff_slice s hc hb p hsmall).mp he)
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) = 2 := by
    have hpos : 0 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) ≠ 1 := fun he => heligible (relIndex_eq_one.mp he)
    change (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 at hslice
    omega
  have hline := selected_forward_kernel_line s hc hb p hslice
  let := finite_Z d.radical t
  let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hHne
  refine ⟨hindex,?_,hline.2,small_forward_line_central s hc hb p hsmall hslice,?_⟩
  · change Nat.card H = 2
    have hh := hline.1
    change Nat.card H ≤ 2 at hh
    omega
  · intro hcentral
    obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
    let A := T.comap i
    have hmA : A.map i = T := map_comap_eq_self (hTG.trans_eq hir.symm)
    have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
      intro x hx
      apply mem_center_iff.mpr
      intro m
      apply hi
      simp only [map_mul]
      apply hcentral
      · have hh := mem_map_of_mem i hx
        rw [map_commutator,hmA,hiU] at hh
        exact hh
      · rw [←hir]
        exact ⟨m,rfl⟩
    have hle := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
    rw [hmA,hiQ] at hle
    exact hHne (le_bot_iff.mp ((commutator_mono
      (DistanceEight.U_le_Z d.radical c) hle).trans_eq (Z_centralizes_Q d.radical c hcol)))

/-- The actual replacement supplies an eligible neighbor of its original
first edge. This is the initial source choice for the backward-selection
argument; eligibility is a proved strict slice index, not an extra input. -/
theorem exists_eligible_first_edge_path_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ (c : Vertex d.radical) (w : (cosetGraph d.radical).Walk c a),
      color d.radical c = false ∧ w.length = 2 ∧
      w.length = (cosetGraph d.radical).dist c a ∧
      w.getVert 1 = p.walk.getVert 1 ∧
      2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb p.start_color hat
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hp : 0 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≠ 1 :=
    fun he => hel (relIndex_eq_one.mp he)
  have hi : 2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by omega
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases he : color d.radical c <;> cases ht : color d.radical (p.walk.getVert 1) <;> simp_all
  have hne : c ≠ a := by
    intro he
    apply hel
    rw [he]
    exact (DistanceEight.U_le_Z d.radical a).trans
      (Escape.EdgeTransfer.Z_le_B hb a p.start_color)
  let w : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hdle : (cosetGraph d.radical).dist c a ≤ 2 := hw ▸ SimpleGraph.dist_le w
  have hdgt : 1 < (cosetGraph d.radical).dist c a :=
    (cosetGraph_connected d.radical).one_lt_dist_of_ne_of_not_adj hne (by
      intro hadj
      exact adjacent_color_ne d.radical ((cosetGraph_adj d.radical _ _).mp hadj)
        (hcol.trans p.start_color.symm))
  exact ⟨c,w,hcol,hw,by omega,rfl,hi⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
