module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedKernel
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Edges

/-!
# The full forward kernel and its commutator line

An actor fixing a hyperplane of either original central cover has action
image of order at most two. Applying the mutual-action bound after adjoining
the cover gives an actual commutator of order at most two. The source forward
kernel is normalized by the starting stabilizer. Its commutator with the
second-vertex moving cover is therefore fixed by their common edge kernel,
and lies in that edge's omega-center seed.

Both inner layers lie in this full forward kernel. Relative normal generation
then bounds the commutator of the entire selected span with the kernel by
the original starting seed. If the selected span is nonabelian, the forward
line has order exactly two and is noncentral at the actual second vertex.
The proof retains the central line of the order-thirty-two cover and uses
no full point-radical image or natural subgroup in place of a quotient.

These are the forward-kernel estimates used in MS93 (5.9), printed
pp.920--921, and (5.12), printed pp.926--927. The relative-generation and
inner-layer calculations adapt the project's SymplecticSetup.ForwardLineAll
and ForwardSpanAll to both full covers and all radical images. The source
slice choice, selected-span nonabelianness, fixed derived subgroup, opposite
core estimates, and both terminal contradictions remain with
qt-e-ms-small-a6-exhaustion-large-distance. In particular the noncentral line
here is not an identification of the source-selected R4/R6 in (5.11).
The unconditional whole-core assembly remains with
qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- A fixed hyperplane of the whole cover bounds its actual commutator by two. -/
theorem cover_small_fixed_commutator_card (A : Subgroup d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) ≤ 2 := by
  let U := replacementMoved d
  let B := U ⊔ A
  let := replacementMoved_normal h d
  let := moved_elementary d
  have hUU : U ≤ centralizer (U : Set d.overgroup) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hfix : U ⊓ centralizer (B : Set d.overgroup) =
      U ⊓ centralizer (A : Set d.overgroup) := by
    apply le_antisymm (fun x hx => ⟨hx.1,fun a ha => hx.2 a (mem_sup_right ha)⟩)
    intro x hx
    refine ⟨hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro b hb
    have hs : B ≤ centralizer ({x} : Set d.overgroup) := by
      apply sup_le
      · intro u hu
        rw [mem_centralizer_singleton_iff]
        exact hUU hx.1 u hu
      · intro a ha
        rw [mem_centralizer_singleton_iff]
        exact hx.2 a ha
    exact mem_centralizer_singleton_iff.mp (hs hb)
  have hBindex : (centralizer (B : Set d.overgroup)).relIndex U ≤ 2 := by
    rw [←inf_relIndex_left, hfix, inf_relIndex_left]
    exact hindex
  have himage : (centralizer (U : Set d.overgroup)).relIndex B ≤ 2 := by
    change (centralizer (replacementMoved d : Set d.overgroup)).relIndex B ≤ 2
    rw [moved_centralizer s, ←s.projection_kernel, relIndex_ker]
    exact cover_small_fixed_index_image s B hBindex
  have hcard := commutator_card_le_two_of_mutual_centralizer_indices U B
    (by rw [normalizer_eq_top]; exact le_top)
    (le_sup_left.trans B.le_normalizer) himage hBindex
  exact (card_le_of_le (commutator_mono le_rfl (show A ≤ B from le_sup_right))).trans hcard

include s in
/-- The full-cover bound in the literal coordinates of any component vertex. -/
theorem moving_small_fixed_commutator_card (hc : DistanceTwo.CentralLayer d)
    {c : Vertex d.radical} (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    Nat.card (⁅U d.radical c,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := cover_small_fixed_commutator_card s (A.comap i) hidx
  rw [←hiU,←hmA,←map_commutator,card_map_of_injective hi]
  exact hh

include s in
/-- The forward slice kernel has a commutator of order at most two, in the
actual common edge seed, for either full central cover. -/
theorem selected_forward_kernel_line (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    Nat.card (⁅U d.radical (p.walk.getVert 2),T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅U d.radical (p.walk.getVert 2),T⁆ ≤ Z d.radical (p.walk.getVert 1) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := U d.radical c ⊓ B d.radical (alpha d.radical)
    ((replacementGeometry h d).Z_normal _)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer (K : Set (FreeAmalgam d.radical))
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
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hfix : K ≤ centralizer (T : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp inf_le_right
  have hidx : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H := K.subgroupOf (U d.radical c)))
    change (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤
      K.relIndex (U d.radical c) at hh
    exact hh.trans (by simpa only [K,inf_relIndex_left] using hslice)
  have hcard : Nat.card H ≤ 2 := moving_small_fixed_commutator_card s hc hcol T hTG hidx
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have htGa : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have htGc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hHN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change H.map (MulAut.conj x).toMonoidHom = H
    dsimp only [H]
    have hUm : (U d.radical c).map (MulAut.conj x).toMonoidHom = U d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c (htGc hx))
    have hTm : T.map (MulAut.conj x).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp (hTN (htGa hx))
    rw [map_commutator,hUm,hTm]
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  let : Finite H := Finite.of_injective (inclusion hHU) (inclusion_injective _)
  have hHC : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    by_cases he : H = ⊥
    · rw [he]; exact bot_le
    · have hh := (one_lt_card_iff_ne_bot H).mpr he
      exact le_centralizer_iff.mp (hHN.trans
        (normalizer_le_centralizer_of_card_two H (by omega)))
  have hUQ : U d.radical c ≤ Q d.radical c :=
    (DistanceEight.U_le_Z d.radical c).trans (by
      apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol)
      rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant c hcol]
      exact replacementDistance_pos h d)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  refine ⟨hcard,?_⟩
  intro x hx
  change x ∈ Z d.radical t
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨(hHU.trans (hUQ.trans (Q_le_adjacent_h d.radical ht hct))) hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical c)) hx),
      hHC hx⟩

include h in
/-- The predecessor seed and full reverse critical kernel lie in the forward kernel. -/
theorem selected_forward_kernel_contains_inner_layers
    (hb : 2 < replacementDistance h d) {e : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) e) :
    Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical e ⊓ Q d.radical (alpha d.radical)) ≤
      Q d.radical (alpha d.radical) ⊓ centralizer
        (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :
          Set (FreeAmalgam d.radical)) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hb4 : 4 ≤ p.walk.length := by
    have he := (replacementGeometry h d).even (alpha d.radical) rfl
    change Even (replacementDistance h d) at he
    rw [Nat.even_iff] at he
    omega
  have hc : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (replacementGeometry h d).even (alpha d.radical) rfl
    change Even (replacementDistance h d) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide)
  have hcd : (cosetGraph d.radical).dist (p.walk.getVert 2)
      (p.walk.getVert (p.walk.length-2)) ≤ p.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4 ≤ p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    exact hh
  have hQc : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hc)
    rw [(replacementGeometry h d).distance_constant _ hc,SimpleGraph.dist_comm,
      p.dist_start (Nat.sub_le _ _)]
    change p.walk.length-2 < replacementDistance h d
    omega
  have hdc : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hc)
    rw [(replacementGeometry h d).distance_constant _ hc,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 2) (p.walk.getVert (p.walk.length-2)) < replacementDistance h d
    omega
  have hde : Z d.radical e ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical e ((replacementGeometry h d).exists_critical e p.end_color)
    rw [(replacementGeometry h d).distance_constant e p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < replacementDistance h d
    omega
  have hcentral : Q d.radical (p.walk.getVert 2) ≤ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :
        Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ hd))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z d.radical _)))
  exact le_inf (sup_le hQc inf_le_right)
    ((sup_le hdc (inf_le_left.trans hde)).trans hcentral)

/-- The small forward slice controls the commutator of the entire selected
span with its full kernel, and hence with the original reverse critical kernel. -/
theorem selected_span_kernel_commutator_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),T⁆ ≤ Z d.radical (alpha d.radical) ∧
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆ ≤ Z d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
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
  have hseed : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    ((Z_le_localZSpan d.radical c (alpha d.radical)).trans (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((replacementGeometry h d).V_local _ rfl hb)
  have hUc : ⁅U d.radical c,T⁆ ≤ Z d.radical (alpha d.radical) :=
    (selected_forward_kernel_line s hc hb p hslice).2.trans (adjacent_Z_le d.radical rfl hat)
  have hZc : ⁅Z d.radical c,T⁆ ≤ Z d.radical (alpha d.radical) := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      _ _ T _ (Z_normalized d.radical _) ((DistanceEight.U_le_Z d.radical c).trans hZcG)
      ((adjacent_Z_le d.radical rfl hat).trans (Z_le_stabilizer d.radical _)) hUc
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hP : ⁅localZSpan d.radical c (alpha d.radical),T⁆ ≤ Z d.radical (alpha d.radical) := by
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) T _ _
      (Z_normalized d.radical _)
    · intro g
      have hgmap : (stabilizer d.radical (alpha d.radical)).map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer
          ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      have hZm : (Z d.radical (alpha d.radical)).map
          (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = Z d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical _
          ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
      rwa [map_commutator,hTm,hZm] at hm
  exact ⟨hP,(commutator_mono le_rfl
    (le_sup_right.trans (selected_forward_kernel_contains_inner_layers (h := h) hb p))).trans hP⟩

/-- If the selected span is nonabelian, its full forward kernel produces a
nonzero line in the common edge seed. The line is noncentral at the actual
second vertex, including for the cover of order thirty-two. -/
theorem selected_forward_kernel_noncentral_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical (p.walk.getVert 2),T⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical (p.walk.getVert 1) ∧
      ¬ H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let P := localZSpan d.radical c (alpha d.radical)
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
  have hseed : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have hHne : H ≠ ⊥ := by
    intro he
    have hZc : Z d.radical c ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
      rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp he) hseed
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
    exact hnonabelian (commutator_eq_bot_iff_le_centralizer.mpr
      (hPC.trans (centralizer_le (selected_span_le_forward_kernel (h := h) hb p))))
  have hline := selected_forward_kernel_line s hc hb p hslice
  let := finite_Z d.radical t
  let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hHne
  refine ⟨?_,hline.2,?_⟩
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

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
