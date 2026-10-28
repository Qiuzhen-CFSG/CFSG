module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCentralIntersection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EdgeKernels
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient

/-!
# The exact radius-kernel tower in the index-four case

Two incident edge kernels with abelian symmetric images, generating the
whole component stabilizer, intersect in its actual two-core. Their
intersection is central modulo that core, and the literal symmetric-six
quotient has trivial center. The proof retains the original projection
and uses no Sylow hypothesis on the original radical.

On a selected critical path this identifies the common interior kernel
and places V_(a') intersect Q_a inside Q_(a+2). If the full radius index
at a is four, the endpoint seed already contributes index two, and radius
escape contributes another factor of at least two. Both factors are
therefore exactly two, and

  V_(a') intersect Q_(a+2) = Z_(a') join (V_(a') intersect Q_a).

The commutator of this entire intermediate kernel with Z_a is exactly the
original critical line. This is the kernel containment and commutator
estimate used at the start of MS93 (5.11)(1), printed p.923. The four-shift
argument from CubeCentralIntersection retains its selected-path witness,
so the final application supplies this whole tower for every original
nonsylow replacement of distance greater than four. Its interior generation
and radius-index hypotheses are discharged there. Both moved covers and all
central attachments remain present.

The final conjugate-kernel control needed to exclude index four is not
proved here. The Sylow and distance-four branches, largeDistance_knownSimple,
and unconditional replacement distance two remain with this task.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6), (5.9), and (5.11), printed pp.917--924. The private EdgeKernels
import reuses the existing edge-derived calculation without changing its
public boundary or rebuilding its earlier consumers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
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
private theorem central_mod_core_le_core (hc : DistanceTwo.CentralLayer d)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (N : Subgroup (FreeAmalgam d.radical)) (hN : N ≤ stabilizer d.radical a)
    (hcomm : ⁅N,stabilizer d.radical a⁆ ≤ Q d.radical a) :
    N ≤ Q d.radical a := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := vertex_coordinates (h := h) hc a ha
  intro x hx
  obtain ⟨y,rfl⟩ := hir.symm ▸ hN hx
  have hcentral : s.projection y ∈ center (Equiv.Perm (Fin 6)) := by
    apply mem_center_iff.mpr
    intro z
    obtain ⟨w,rfl⟩ := s.surjective z
    have hmem : i ⁅y,w⁆ ∈ (pCore 2 d.overgroup).map i := by
      rw [map_commutatorElement,hiQ]
      exact hcomm (commutator_mem_commutator hx (hir ▸ (show i w ∈ i.range from ⟨w,rfl⟩)))
    have hcore : ⁅y,w⁆ ∈ pCore 2 d.overgroup := (mem_map_iff_mem hi).mp hmem
    rw [←s.projection_kernel,MonoidHom.mem_ker,map_commutatorElement] at hcore
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcore).symm
  rw [Theory.SpecificGroups.SymmetricSix.s6_center_eq_bot,mem_bot] at hcentral
  rw [←hiQ]
  apply mem_map_of_mem
  rwa [←s.projection_kernel,MonoidHom.mem_ker]

include s in
/-- Generating incident kernels with abelian images intersect in precisely
the original component two-core. -/
theorem abelian_generating_edge_kernels_inf
    (hc : DistanceTwo.CentralLayer d)
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t v : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hav : Adjacent d.radical a v)
    (hgen : Q d.radical t ⊔ Q d.radical v = stabilizer d.radical a) :
    Q d.radical t ⊓ Q d.radical v = Q d.radical a := by
  have hlocal {w : Vertex d.radical} (haw : Adjacent d.radical a w) :
      Q d.radical a ≤ Q d.radical w := by
    have ht : color d.radical w=true := by
      have hh := adjacent_color_ne d.radical haw
      rw [ha] at hh
      cases he : color d.radical w <;> simp_all
    exact Q_le_adjacent_h d.radical ht haw
  apply le_antisymm _ (le_inf (hlocal hat) (hlocal hav))
  apply central_mod_core_le_core s hc ha _
    (inf_le_left.trans (show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)))
  rw [commutator_comm,←hgen]
  apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Q d.radical t) (Q d.radical v) (Q d.radical t ⊓ Q d.radical v)
    (Q d.radical a) (Q_normalized d.radical a)
    (le_sup_left.trans_eq hgen) (le_sup_right.trans_eq hgen)
  · exact (commutator_mono le_rfl inf_le_left).trans
      (edge_derived_le_core_of_abelian_image s hab ha hat)
  · exact (commutator_mono le_rfl inf_le_right).trans
      (edge_derived_le_core_of_abelian_image s hab ha hav)

include e hz hn in
/-- On a selected critical path the opposite radius kernel in the starting
core lies in the first interior component core. -/
theorem nonsylow_radius_kernel_le_interior_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    V d.radical a' ⊓ Q d.radical a ≤ Q d.radical (p.walk.getVert 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
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

private theorem index_four_kernel_tower {F : Type*} [Group F]
    (V Z A C : Subgroup F) [Finite V]
    (hZV : Z ≤ V) (hZC : Z ≤ C) (hJC : V ⊓ A ≤ C)
    (hZA : A.relIndex Z=2) (hVA : A.relIndex V=4) (hVC : ¬ V ≤ C) :
    C.relIndex V=2 ∧ A.relIndex (V ⊓ C)=2 ∧
      V ⊓ C = Z ⊔ (V ⊓ A) := by
  let J := V ⊓ A
  let K := V ⊓ C
  have hJK : J ≤ K := le_inf inf_le_left hJC
  have hZK : Z ≤ K := le_inf hZV hZC
  let : Finite K := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hCK : 2 ≤ C.relIndex V := by
    have hpos : 0 < C.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : C.relIndex V ≠ 1 := fun hh => hVC (relIndex_eq_one.mp hh)
    omega
  have hAK : 2 ≤ A.relIndex K := by
    rw [←hZA]
    exact relIndex_le_of_le_right hZK index_ne_zero_of_finite
  have hAC : V ⊓ (A ⊓ C) = V ⊓ A :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
      (le_inf inf_le_left (le_inf inf_le_right hJC))
  have heq : (A ⊓ C).relIndex V=A.relIndex V := by
    have hh := congrArg (fun N : Subgroup F => N.relIndex V) hAC
    simpa only [inf_relIndex_left] using hh
  have ht := relIndex_inf_mul_relIndex A C V
  rw [heq,hVA,inf_comm C V] at ht
  have hC : C.relIndex V=2 := by
    change A.relIndex K * C.relIndex V=4 at ht
    nlinarith
  have hA : A.relIndex K=2 := by
    change A.relIndex K * C.relIndex V=4 at ht
    rw [hC] at ht
    omega
  refine ⟨hC,hA,?_⟩
  let E := Z ⊔ J
  have hEK : E ≤ K := sup_le hZK hJK
  have hJE : J ≤ E := le_sup_right
  let : Finite E := Finite.of_injective (inclusion hEK) (inclusion_injective _)
  have hJKidx : J.relIndex K=2 := by
    have hh : K ⊓ J = K ⊓ A := by
      dsimp only [K,J]
      ext x
      simp only [mem_inf]
      tauto
    have hh' := congrArg (fun N : Subgroup F => N.relIndex K) hh
    rw [inf_relIndex_left,inf_relIndex_left] at hh'
    exact hh'.trans hA
  have hJZ : J.relIndex Z=2 := by
    have hh : Z ⊓ J=Z ⊓ A := by
      apply le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      exact le_inf inf_le_left (le_inf (inf_le_left.trans hZV) inf_le_right)
    have hh' := congrArg (fun N : Subgroup F => N.relIndex Z) hh
    rw [inf_relIndex_left,inf_relIndex_left] at hh'
    exact hh'.trans hZA
  have hJEidx : 2 ≤ J.relIndex E := by
    rw [←hJZ]
    exact relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite
  have hpos : 0 < E.relIndex K := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hmul := relIndex_mul_relIndex J E K hJE hEK
  rw [hJKidx] at hmul
  have hone : E.relIndex K=1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hone) hEK

include e hz hn in
/-- The equality-four case has two exact index-two steps. Its intermediate
kernel is the full endpoint seed times the original radius kernel. -/
theorem nonsylow_radius_four_kernel_tower_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
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
  have hescape := nonsylow_radius_escape_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns rev
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
    (nonsylow_radius_kernel_le_interior_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p hgen)
    (nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p).2.1
    hfour hescape

include e hz hn in
/-- In the equality-four case, the whole interior radius kernel has exactly
the original critical commutator against the starting seed. -/
theorem nonsylow_radius_four_kernel_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (hfour : (Q d.radical a).relIndex (V d.radical a')=4) :
    ⁅V d.radical a' ⊓ Q d.radical (p.walk.getVert 2),Z d.radical a⁆ =
      ⁅Z d.radical a',Z d.radical a⁆ := by
  have ht := nonsylow_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour
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
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    ∃ a a' : Vertex d.radical,
      ∃ p : CriticalPath d.radical (replacementGeometry h d) a a',
        (Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
          stabilizer d.radical (p.walk.getVert 2)) ∧
        (Q d.radical a).relIndex (V d.radical a')=4 := by
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hb6 : 6 < replacementDistance h d
  · obtain ⟨v⟩ := nonsylow_edge_paired_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p
    obtain ⟨q,r,t,_,_,_,hact₄,hact₆⟩ := nonsylow_edge_paired_terminal_radius_actions_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns v.path
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
        · have hn₄ := nonsylow_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hns p v q r hv hq
          have hn₆ := nonsylow_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hns v.path q r t hq hr
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
    obtain ⟨q,r,t,_,_,_,_,_,hi⟩ := nonsylow_edge_paired_terminal_six_knownSimple
      (e := e) (hz := hz) (hn := hn) heq hns p
    exact ⟨_,_,r.path,r.first_interior_generation (by omega),hi⟩


include e hz hn in
/-- Every original nonsylow replacement above distance four realizes the
exact two-step kernel tower on an actual selected critical path. -/
theorem nonsylow_four_lt_exists_radius_kernel_tower_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
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
    (e := e) (hz := hz) (hn := hn) hb hns
  obtain ⟨hi,hj,hK⟩ := nonsylow_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour
  exact ⟨a,a',p,hgen,hfour,hi,hj,hK,nonsylow_radius_four_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
