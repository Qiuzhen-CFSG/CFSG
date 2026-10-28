module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeConjugateKernel

/-!
# Excluding distance greater than four for elementary replacement images

The generated path from SylowRadius has endpoint-radius index four. Its
literal kernel tower has two index-two steps. Equal small critical
commutators identify the full seed kernels, including the central attachment,
and put the selected kernel inside the cubic-conjugate intermediate core.
The kernel joined with the central seed is normalized by both endpoint seeds
and the selected edge kernel. Their proved generation equation places it in
the Baumann slice, contradicting the strict forward-slice bound.

The resulting distance bound applies to every minimum characteristic
replacement with elementary canonical radical image, including original
Sylow radicals. Positivity and parity give the two-or-four alternative for
the literal replacement, and the chosen original replacement is an actual
consumer. Combined with the original-Sylow restriction, every branch still
above four has a non-elementary image of order eight or sixteen. The
non-elementary branches and the distance-four exclusion remain necessary
for the unconditional large-distance theorem.

This extends the existing CubeRadiusKernel and CubeConjugateKernel proofs
using the constructed elementary-image paths and strict slices. The private
imports reuse their numerical kernel-tower and index-two group lemmas.
Both moved covers, full centers, original radicals and actual graph maps
are preserved throughout.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6), (5.9)--(5.11), printed pp.917--924, especially the two
conjugate-seed cases and the final radius comparison on pp.923--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowTerminal
open CubePairedEdges CubeCommonFixer CubeRadiusAction NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- On a selected critical path the opposite radius kernel in the starting
core lies in the first interior component core. -/
theorem elementary_radius_kernel_le_interior_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    V d.radical a' ⊓ Q d.radical a ≤ Q d.radical (p.walk.getVert 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hfull' : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
    rw [hfull']
    let : IsElementaryAbelian 2 (CFSG.Quasithin.ChapterB.Offenders.D 6) :=
      elementary_disjointTranspositions (3 : Fin 4)
    let : IsElementaryAbelian 2 ((CFSG.Quasithin.ChapterB.Offenders.D 6).map
        (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have ha₂ : color d.radical (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have h₂₁ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have h₂₃ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  rw [←abelian_generating_edge_kernels_inf s hc hab ha₂ h₂₁ h₂₃ hgen]
  apply le_inf
  · have ha₁ : Adjacent d.radical a (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have ht : color d.radical (p.walk.getVert 1)=true := by
      have hh := adjacent_color_ne d.radical ha₁
      rw [p.start_color] at hh
      cases he : color d.radical (p.walk.getVert 1) <;> simp_all
    exact inf_le_right.trans (Q_le_adjacent_h d.radical ht ha₁)
  · apply inf_le_left.trans
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-3+2 < replacementDistance h d
    omega

include e hz hn in
/-- The equality-four case has two exact index-two steps. Its intermediate
kernel is the full endpoint seed times the original radius kernel. -/
theorem elementary_radius_four_kernel_tower_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (hfour : (Q d.radical a).relIndex (V d.radical a')=4) :
    (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a')=2 ∧
      (Q d.radical a).relIndex (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))=2 ∧
      V d.radical a' ⊓ Q d.radical (p.walk.getVert 2) =
        Z d.radical a' ⊔ (V d.radical a' ⊓ Q d.radical a) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have hZC : Z d.radical a' ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < replacementDistance h d
    omega
  let rev : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],critical_reverse_pair s hc p⟩
  have hescape := SylowEscape.elementary_radius_escape_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage rev
  change ¬ V d.radical a' ≤ Q d.radical
    (p.walk.reverse.getVert (p.walk.reverse.length-2)) at hescape
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show p.walk.length-(p.walk.length-2)=2 by omega] at hescape
  have hVQ := V_le_Q d.radical (geometry := replacementGeometry h d) p.end_color
    (show 2 < replacementDistance h d by omega)
  let := finite_stabilizer d.radical a'
  let : Finite (V d.radical a') := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  exact index_four_kernel_tower _ _ _ _ (Z_le_VBall d.radical _ 2) hZC
    (elementary_radius_kernel_le_interior_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p hgen)
    (SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).2.1
    hfour hescape

include e hz hn in
/-- In the equality-four case, the whole interior radius kernel has exactly
the original critical commutator against the starting seed. -/
theorem elementary_radius_four_kernel_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (hfour : (Q d.radical a).relIndex (V d.radical a')=4) :
    ⁅V d.radical a' ⊓ Q d.radical (p.walk.getVert 2),Z d.radical a⁆ =
      ⁅Z d.radical a',Z d.radical a⁆ := by
  have ht := elementary_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour
  rw [ht.2.2]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  let J := ⁅Z d.radical a',Z d.radical a⁆
  have hJZ : J ≤ Z d.radical a' := by
    dsimp only [J]
    rw [commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a')
  have hQN : Q d.radical a' ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le hJZ)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hVQ := V_le_Q d.radical (geometry := replacementGeometry h d) p.end_color
    (show 2 < replacementDistance h d by omega)
  apply commutator_sup_le_of_relative_normal (Q d.radical a')
    (Z d.radical a') (V d.radical a' ⊓ Q d.radical a) (Z d.radical a) J hQN
    ((Z_le_VBall d.radical a' 2).trans hVQ) (inf_le_left.trans hVQ) le_rfl
  exact (commutator_mono inf_le_right le_rfl).trans
    (by rw [commutator_comm,Z_centralizes_Q d.radical a p.start_color]; exact bot_le)

include e hz hn in
private theorem exists_generated_radius_four
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ a a' : Vertex d.radical,
      ∃ p : CriticalPath d.radical (replacementGeometry h d) a a',
        (Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
          stabilizer d.radical (p.walk.getVert 2)) ∧
        (Q d.radical a).relIndex (V d.radical a')=4 := by
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hb6 : 6 < replacementDistance h d
  · obtain ⟨v⟩ := elementary_edge_paired_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage p
    obtain ⟨q,r,t,_,_,_,hact₄,hact₆⟩ := elementary_edge_paired_terminal_radius_actions_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage v.path
    have small {c z : Vertex d.radical}
        (w : CriticalPath d.radical (replacementGeometry h d) c z)
        (hh : (Q d.radical c).relIndex (V d.radical z) ≤ 4) :
        (Q d.radical c).relIndex (V d.radical z)=4 :=
      (small_opposite_radius_eq_four_knownSimple (e := e) (hz := hz) (hn := hn)
        (by omega) w hh).2.2
    by_cases hv : 4 < (Q d.radical v.start).relIndex (V d.radical (p.walk.getVert (p.walk.length-2)))
    · by_cases hq : 4 < (Q d.radical q.start).relIndex
          (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))
      · by_cases hr : 4 < (Q d.radical r.start).relIndex
            (V d.radical (q.path.walk.getVert (q.path.walk.length-2)))
        · have hn₄ := elementary_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hEimage p v q r hv hq
          have hn₆ := elementary_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hEimage v.path q r t hq hr
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          have hi₄ : (Q d.radical q.start).relIndex (V d.radical z₄) ≤ 2 := by
            by_contra! hh
            exact hn₄ (hact₄ hh)
          have hi₆ : (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) ≤ 2 := by
            by_contra! hh
            exact hn₆ (hact₆ hh)
          have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
            V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
              (by change 2 < replacementDistance h d; omega)
          let := finite_stabilizer d.radical z₄
          let : Finite (V d.radical z₄) := Finite.of_injective
            (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
          have htower := relIndex_inf_mul_relIndex (Q d.radical r.start)
            (Q d.radical q.start) (V d.radical z₄)
          rw [inf_comm (Q d.radical q.start)] at htower
          have hmono : (Q d.radical r.start).relIndex (V d.radical z₄) ≤
              (Q d.radical r.start ⊓ Q d.radical q.start).relIndex (V d.radical z₄) :=
            relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
          have hupper : (Q d.radical r.start).relIndex (V d.radical z₄) ≤ 4 := by
            rw [←htower] at hmono
            exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
          exact ⟨_,_,r.path,r.first_interior_generation (by omega),small r.path hupper⟩
        · exact ⟨_,_,r.path,r.first_interior_generation (by omega),small r.path (Nat.le_of_not_gt hr)⟩
      · exact ⟨_,_,q.path,q.first_interior_generation (by omega),small q.path (Nat.le_of_not_gt hq)⟩
    · exact ⟨_,_,v.path,v.first_interior_generation (by omega),small v.path (Nat.le_of_not_gt hv)⟩
  · have heven := replacementDistance_even h d
    rw [Nat.even_iff] at heven
    have heq : replacementDistance h d=6 := by omega
    obtain ⟨q,r,t,_,_,_,_,_,hi⟩ := elementary_edge_paired_terminal_six_knownSimple
      (e := e) (hz := hz) (hn := hn) heq hEimage p
    exact ⟨_,_,r.path,r.first_interior_generation (by omega),hi⟩

include e hz hn in
/-- Every original elementary-image replacement above distance four realizes the
exact two-step kernel tower on an actual selected critical path. -/
theorem elementary_four_lt_exists_radius_kernel_tower_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ a a' : Vertex d.radical,
      ∃ p : CriticalPath d.radical (replacementGeometry h d) a a',
        (Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
          stabilizer d.radical (p.walk.getVert 2)) ∧
        (Q d.radical a).relIndex (V d.radical a')=4 ∧
        (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a')=2 ∧
        (Q d.radical a).relIndex (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))=2 ∧
        V d.radical a' ⊓ Q d.radical (p.walk.getVert 2) =
          Z d.radical a' ⊔ (V d.radical a' ⊓ Q d.radical a) ∧
        ⁅V d.radical a' ⊓ Q d.radical (p.walk.getVert 2),Z d.radical a⁆ =
          ⁅Z d.radical a',Z d.radical a⁆ := by
  obtain ⟨a,a',p,hgen,hfour⟩ := exists_generated_radius_four
    (e := e) (hz := hz) (hn := hn) hb hEimage
  obtain ⟨hi,hj,hK⟩ := elementary_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour
  exact ⟨a,a',p,hgen,hfour,hi,hj,hK,elementary_radius_four_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour⟩

include e hz hn in
/-- At radius index two, the selected critical seed and its cubic conjugate
have identical nontrivial commutators whenever both escape the same core.
The common line is fixed by the whole intermediate stabilizer. -/
theorem elementary_paired_radius_two_common_line_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2)
    (hout : ¬ Z d.radical (act d.radical q.cubic⁻¹ q.start) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ =
      ⁅Z d.radical (act d.radical q.cubic⁻¹ q.start),Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ∧
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have hac : (cosetGraph d.radical).dist a c+2 = replacementDistance h d := by
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hVG := radius_le_stabilizer_of_dist (h := h) p.start_color hac.le
  have hVQ := V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color
    (show 2 < replacementDistance h d by omega)
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hVmap : (V d.radical a).map (MulAut.conj q.cubic).toMonoidHom = V d.radical a := by
    rw [←inv_inv q.cubic,←V_act]
    rw [show act d.radical q.cubic⁻¹ a=a from (stabilizer d.radical a).inv_mem hx]
  have hZV' : Z d.radical (act d.radical q.cubic⁻¹ q.start) ≤ V d.radical a := by
    rw [Z_act,inv_inv,←hVmap]
    exact map_mono hZV
  have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.path.end_color))
  have heq : ⁅Z d.radical q.start,Z d.radical c⁆ =
      ⁅Z d.radical (act d.radical q.cubic⁻¹ q.start),Z d.radical c⁆ := by
    rw [commutator_comm (Z d.radical q.start),
      commutator_comm (Z d.radical (act d.radical q.cubic⁻¹ q.start))]
    exact (index_two_commutator _ _ _ _ hZV hi q.path.critical.2 hQC
      (hVG.trans (Z_normalized d.radical c))).trans
        (index_two_commutator _ _ _ _ hZV' hi hout hQC
          (hVG.trans (Z_normalized d.radical c))).symm
  refine ⟨heq,?_⟩
  have hline := SylowCritical.elementary_paired_shift_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hZcQa : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.path.end_color)
    rw [(replacementGeometry h d).distance_constant c q.path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist a c < replacementDistance h d
    omega
  have hQmap : (Q d.radical a).map (MulAut.conj q.cubic).toMonoidHom=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized d.radical a) hx)
  have hZcEdge : Z d.radical c ≤ Q d.radical (act d.radical q.cubic⁻¹ q.edge) := by
    rw [Q_act,inv_inv]
    exact hZcQa.trans (hQmap ▸ map_mono (Q_le_adjacent_h d.radical ht q.adjacent_start))
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hEdge := cube_edge_seed_commutator_le s hc u hR
    ((action_preserves_color d.radical _ _).trans q.path.start_color)
    ((adjacent_act_iff d.radical q.cubic⁻¹ _ _).mpr q.adjacent_shift)
  have hlineEdge : ⁅Z d.radical q.start,Z d.radical c⁆ ≤
      Z d.radical (act d.radical q.cubic⁻¹ q.edge) := by
    rw [heq]
    exact (commutator_mono le_rfl hZcEdge).trans hEdge
  have hfixed : ⁅Z d.radical q.start,Z d.radical c⁆ ≤ centralizer
      (Q d.radical (act d.radical q.cubic⁻¹ q.edge) : Set (FreeAmalgam d.radical)) := by
    intro v hv
    have hh := hlineEdge hv
    rw [Z,if_neg (by rw [action_preserves_color,ht]; decide)] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply le_centralizer_iff.mpr
  rw [←q.kernel_generation]
  apply sup_le (le_centralizer_iff.mp hline.2.2.2.1)
  have hh := le_centralizer_iff.mp hfixed
  rwa [Q_act,inv_inv] at hh

include e hz hn in
/-- The literal seed kernel is contained in the core conjugated by the
same selected cubic. Both the trapped and escaping conjugate-seed cases
are discharged; no additional centrality premise is imposed. -/
theorem elementary_paired_radius_two_conjugate_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical q.cubic (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  let w := act d.radical q.cubic⁻¹ q.start
  have hcancel : act d.radical q.cubic w=q.start := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z d.radical w ≤ Q d.radical c
  · have hh := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hline := elementary_paired_radius_two_common_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q hi hout
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have hac : (cosetGraph d.radical).dist a c+2 = replacementDistance h d := by
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hwa : (cosetGraph d.radical).dist w a ≤ 2 := by
    conv_lhs => rhs; rw [←show act d.radical q.cubic⁻¹ a=a from (stabilizer d.radical a).inv_mem hx]
    rw [show w=act d.radical q.cubic⁻¹ q.start from rfl,dist_act]
    exact hnear
  have hw : color d.radical w=false :=
    (action_preserves_color d.radical _ _).trans q.path.start_color
  have hpair : CriticalPair d.radical w c ((replacementGeometry h d).exists_critical w hw) := by
    refine ⟨?_,hout⟩
    apply le_antisymm _ (criticalDistance_le d.radical w _ hout)
    rw [(replacementGeometry h d).distance_constant w hw]
    have ht : (cosetGraph d.radical).dist w c ≤
        (cosetGraph d.radical).dist w a + (cosetGraph d.radical).dist a c :=
      (cosetGraph_connected d.radical).dist_triangle
    change _ ≤ replacementDistance h d
    omega
  let r := CriticalPath.ofPair (geometry := replacementGeometry h d) hw hpair
  obtain ⟨t⟩ : Nonempty (CriticalPath d.radical (replacementGeometry h d) q.start
      (act d.radical q.cubic c)) := by
    rw [←hcancel]
    exact ⟨r.act q.cubic⟩
  let H := ⁅Z d.radical q.start,Z d.radical c⁆
  have hHmap : H.map (MulAut.conj q.cubic⁻¹).toMonoidHom=H :=
    mem_normalizer_iff_map_conj_eq.mp
      (((le_centralizer_iff.mp hline.2).trans (Subgroup.centralizer_le_normalizer _))
        ((stabilizer d.radical a).inv_mem hx))
  have heq : ⁅Z d.radical q.start,Z d.radical c⁆ =
      ⁅Z d.radical q.start,Z d.radical (act d.radical q.cubic c)⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj q.cubic⁻¹).toMonoidHom) hline.1
    change H.map (MulAut.conj q.cubic⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  have hp : (Q d.radical c).relIndex (Z d.radical q.start)<4 := by
    rw [(SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path).1]
    decide
  have ht : (Q d.radical (act d.radical q.cubic c)).relIndex (Z d.radical q.start)<4 := by
    rw [(SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage t).1]
    decide
  exact (small_critical_equal_commutators_kernel s hc q.path t hp ht heq).le.trans inf_le_right

include e hz hn in
private theorem paired_radius_two_control_false
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2)
    (hcontrol : ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),Z d.radical a'⁆ ≤
      Z d.radical a) : False := by
  let c := p.walk.getVert (p.walk.length-2)
  let K := Z d.radical q.start ⊓ Q d.radical c
  let Y := K ⊔ Z d.radical a
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hb2 : 2 < replacementDistance h d := by omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hKV : K ≤ V d.radical a := inf_le_left.trans hZV
  have hYV : Y ≤ V d.radical a := sup_le hKV (Z_le_VBall d.radical _ 2)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color hb2).trans (fun _ hx => hx.1)
  have hline := SylowCritical.elementary_paired_shift_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q
  have hsmall : (Q d.radical c).relIndex (Z d.radical q.start)<4 := by
    rw [(SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path).1]
    decide
  have hKN : Q d.radical q.edge ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := (small_critical_kernel_normalized_iff_first_seed s hc q.path hsmall).mpr
      (q.first.symm ▸ hline.2.1)
    simpa only [q.first] using hh
  have hKG : K ≤ stabilizer d.radical a := hKV.trans hVG
  have hKmove : ⁅K,Z d.radical a'⁆ ≤ Z d.radical a :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans hcontrol
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hZmap : (Z d.radical a).map (MulAut.conj q.cubic⁻¹).toMonoidHom=Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized d.radical a) ((stabilizer d.radical a).inv_mem hx))
  have hVmap : (V d.radical a).map (MulAut.conj q.cubic⁻¹).toMonoidHom=V d.radical a := by
    rw [←V_act,show act d.radical q.cubic a=a from hx]
  have hKother := elementary_paired_radius_two_conjugate_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q hi
  have hKmove' : ⁅K,Z d.radical (act d.radical q.cubic a')⁆ ≤ Z d.radical a := by
    have hm := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hcontrol
    rw [map_commutator,map_inf _ _ _ (MulAut.conj q.cubic⁻¹).injective,hVmap,←Q_act,←Z_act,hZmap] at hm
    exact (commutator_mono (le_inf hKV hKother) le_rfl).trans hm
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hA'G : Z d.radical (act d.radical q.cubic a') ≤ stabilizer d.radical a := by
    have hm := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hAG
    rw [←Z_act,←stabilizer_act,show act d.radical q.cubic a=a from hx] at hm
    exact hm
  have hYmove (A : Subgroup (FreeAmalgam d.radical))
      (hA : A ≤ stabilizer d.radical a) (hK : ⁅K,A⁆ ≤ Z d.radical a) :
      ⁅Y,A⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      K (Z d.radical a) A (Z d.radical a) (Z_normalized d.radical a)
      hKG (Z_le_stabilizer d.radical a) hK
    exact le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized d.radical a))
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←q.endpoint_generation]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_trans (le_inf hKN _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      exact (show Q d.radical q.edge ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_start)).trans (Z_normalized d.radical a)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hAG hKmove).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hA'G hKmove').trans le_sup_right)
  have hKB : K ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb2 p.start_color Y (Z d.radical a')
      hYV hYN hAG (critical_reverse_pair s hc p).2 (hYmove _ hAG hKmove))
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by
    have hBmap : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 a p.start_color
        ((stabilizer d.radical a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj q.transporter⁻¹).injective]
    exact SylowCritical.elementary_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p
  let := finite_Z d.radical q.start
  let : Finite (U d.radical q.start) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical q.start)) (inclusion_injective _)
  have hupper : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) ≤ 2 := by
    have hh := (relIndex_le_of_le_left hKB (L := U d.radical q.start) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (H := K) (DistanceEight.U_le_Z d.radical q.start) index_ne_zero_of_finite)
    have hidx : K.relIndex (Z d.radical q.start)=2 := by
      dsimp only [K]
      rw [inf_relIndex_left]
      exact (SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path).1
    exact hh.trans_eq hidx
  exact (Nat.not_le_of_gt hstrict) hupper

include e hz hn in
/-- The exact radius-index-four tower is impossible on a path with the
actual generating interior kernels. This is the strict-growth step of (5.11). -/
theorem elementary_generated_radius_ne_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    (Q d.radical a).relIndex (V d.radical a') ≠ 4 := by
  intro hfour
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let rev : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have he : rev.walk.getVert (rev.walk.length-2)=p.walk.getVert 2 := by
    dsimp only [rev]
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega
  have ht := elementary_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour
  have hcomm := elementary_radius_four_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour
  obtain ⟨q⟩ := SylowCritical.elementary_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage rev
  apply paired_radius_two_control_false (e := e) (hz := hz) (hn := hn) hb hEimage rev q
  · simpa only [he] using ht.1
  · rw [he,hcomm,commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a')

include e hz hn in
/-- Every minimum characteristic replacement of an original elementary-image
radical has critical distance at most four. All index, conjugate-kernel,
and strict-slice premises are discharged on the original graph. -/
theorem elementary_replacementDistance_le_four_knownSimple
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    replacementDistance h d ≤ 4 := by
  by_contra! hb
  obtain ⟨a,a',p,hgen,hfour,_⟩ := elementary_four_lt_exists_radius_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  exact elementary_generated_radius_ne_four_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p hgen hfour


/-- Positivity and parity turn the elementary-image bound into the exact
two remaining distances, on the literal minimum characteristic replacement. -/
theorem elementary_replacementDistance_two_or_four_knownSimple
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    replacementDistance h d = 2 ∨ replacementDistance h d = 4 := by
  have hb := elementary_replacementDistance_le_four_knownSimple hEimage
  have hp := replacementDistance_pos h d
  have he := replacementDistance_even h d
  rw [Nat.even_iff] at he
  omega

/-- The elementary branch of source (5.11) for the chosen original
replacement, with every local path and strict-slice premise discharged. -/
theorem original_elementary_distance_two_or_four_knownSimple
    (hEimage : IsElementaryAbelian 2
      ((replacement h).radical.map
        (SourceReduction.projection h e hz hn (replacement h)))) :
    replacementDistance h (replacement h) = 2 ∨
      replacementDistance h (replacement h) = 4 :=
  elementary_replacementDistance_two_or_four_knownSimple hEimage

/-- Every branch still above four has a non-elementary canonical image.
The Sylow assertion concerns the original radical, while both restriction
indices and image orders concern the actual characteristic replacement. -/
theorem four_lt_original_sylow_non_elementary_image_knownSimple
    (hb : 4 < replacementDistance h d) :
    (∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      (¬ IsElementaryAbelian 2
        (d.radical.map (SourceReduction.projection h e hz hn d))) ∧
      ((d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 1 ∧
        Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) ∨
       (d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 2 ∧
        Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)) := by
  obtain ⟨hs,hi⟩ := MixedExclusion.four_lt_original_sylow_large_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  exact ⟨hs,fun hEimage => (Nat.not_le_of_gt hb)
    (elementary_replacementDistance_le_four_knownSimple hEimage),hi⟩

end SylowTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
