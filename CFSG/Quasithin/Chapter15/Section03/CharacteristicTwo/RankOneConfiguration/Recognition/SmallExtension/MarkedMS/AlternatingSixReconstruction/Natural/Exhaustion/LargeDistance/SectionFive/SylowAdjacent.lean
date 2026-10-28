module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
public import Theory.GroupTheory.SmallMoverEqualOrder
public import Theory.GroupTheory.SmallMoverNormalizer
public import Theory.Representation.BinaryOffender.QuadraticDualOffender
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.QuadraticSylow

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelEdges
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair

/-!
# Unequal neighboring small movers on the original natural graph

Above critical distance four, normal quadratic actors in the actual edge
normalizer lie in its maximum small mover. This follows from the marked
Sylow subgroup of S₆ and its quadratic three-pair subgroup, on either full
moved cover. Transport uses the literal edge embedding into the free amalgam.

When the replacement radical image has order sixteen, its edge normalizer
is the edge core. Two unequal neighboring small movers are normal subgroups
of index two: they generate that core, intersect with index four, and each
acts nonquadratically on the other's moved cover. Equal orders also give
the strict fixed-index bound required by the source comparison.

The critical-path application selects a line-moving element inside the
second mover. Its transported path fixes the first three vertices and keeps
both full critical kernels, their join, and their invariant intersection.
The critical-line movement and inequality of neighboring movers remain
explicit branch premises; backward selection and the terminal distance
exclusions are not asserted here. Both central covers and the original
graph and quotient maps are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.4)--(5.5), printed pp.915--917, especially the comparison of
neighboring small movers on p.916.
-/

public noncomputable section
open Theory.GroupTheory
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

private theorem cube_actor_commutator_fixed (s : FullSymmetricAction h e hz hn d)
    (A : Subgroup d.overgroup) (u : S)
    (hR : A.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom) :
    ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup) := by
  let := replacementMoved_normal h d
  apply commutator_le.mpr
  intro v hv r hr k hk
  have hm : ⁅v,r⁆ ∈ replacementMoved d :=
    (commutator_le_left (replacementMoved d) A) (commutator_mem_commutator hv hr)
  let w : Additive (replacementMoved d) := Additive.ofMul ⟨⁅v,r⁆,hm⟩
  have he : coverAction s (s.projection k) w=w := by
    dsimp only [w]
    rw [NormalElementaryQuotient.vector_commutator (replacementMoved d)
      s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)
      ⟨v,hv⟩ r]
    have hh := CubeKernelEdges.model_quadratic (coverAction s) (cover_model s)
      u (s.projection r) (s.projection k)
      (hR (mem_map_of_mem _ hr)) (hR (mem_map_of_mem _ hk)) (Additive.ofMul ⟨v,hv⟩)
    change coverAction s (s.projection k)
      (Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)) =
      Additive.ofMul ⟨v,hv⟩-coverAction s (s.projection r) (Additive.ofMul ⟨v,hv⟩)
    simpa only [map_sub,neg_sub] using congrArg Neg.neg hh
  have he' := congrArg (fun a : Additive (replacementMoved d) => (a.toMul : d.overgroup)) he
  rw [coverAction_conjugate] at he'
  exact mul_inv_eq_iff_eq_mul.mp he'


include e hz hn in
/-- Every normal quadratic actor in the actual radical normalizer belongs
to its maximum small mover, on either full moved cover. -/
theorem normalizer_quadratic_le_small_mover_knownSimple
    (hb : 4 < replacementDistance h d) (A : Subgroup d.overgroup)
    (hA : A ≤ normalizer (d.radical : Set d.overgroup))
    (hnA : normalizer (d.radical : Set d.overgroup) ≤ normalizer (A : Set d.overgroup))
    (hquad : ⁅⁅replacementMoved d,A⁆,A⁆ = ⊥) :
    A ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨u,hN,_,hJ,_,_,_,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map f = B := by
    rw [map_map]
    have he : f.comp (MulAut.conj u).toMonoidHom = MonoidHom.id S := by
      ext x
      simp [f]
    rw [he,map_id]
  have hqu : QuadraticPointCore.Quadratic (A.map s.projection) :=
    image_quadratic_of_commutator s A (commutator_eq_bot_iff_le_centralizer.mp hquad)
  have hq : QuadraticPointCore.Quadratic ((A.map s.projection).map f) :=
    QuadraticPointCore.quadratic_conjugate _ hqu u⁻¹
  let : IsElementaryAbelian 2 ((A.map s.projection).map f) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _ hq
  have hle : (A.map s.projection).map f ≤ sylowCarrier := by
    have hh := map_mono (f := f) (map_mono (f := s.projection) hA)
    rw [hN,back] at hh
    exact hh
  have hnorm : sylowCarrier ≤ normalizer (((A.map s.projection).map f : Subgroup S) : Set S) := by
    have hh := (map_mono (f := s.projection) hnA).trans (le_normalizer_map s.projection)
    have hh := (map_mono (f := f) hh).trans (le_normalizer_map f)
    rwa [hN,back] at hh
  have hD := QuadraticSylow.normal_quadratic_le_cube _ hle hnorm hq
  have him : A.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u⁻¹).injective).mp
    rwa [back]
  rw [hJ]
  exact le_inf hA (map_le_iff_le_comap.mp him)

include h in
private theorem edge_coordinates (hc : DistanceTwo.CentralLayer d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨hga,hgt⟩
    rw [hga,hgt]
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
    · rw [MonoidHom.range_comp]
      have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
        (stabilizer_m_base d.radical).symm
      rw [he]
      simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := U_act d.radical g (alpha d.radical)
      rw [hc.U_eq_moved] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at ha
    cases ha

include e hz hn in
/-- The same normal-quadratic control in the literal relative edge normalizer,
transported without discarding the central attachment. -/
theorem edge_normalizer_quadratic_le_small_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a)
    (hnA : normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a ≤
      normalizer (A : Set (FreeAmalgam d.radical)))
    (hquad : ⁅⁅U d.radical a,A⁆,A⁆ = ⊥) :
    A ≤ SmallMover.join (U d.radical a) (Q d.radical a)
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) 4 := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  have hiN : N.map i = T := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hA.trans inf_le_right).trans_eq hir.symm)
  have hA₀ : A.comap i ≤ N := by
    have hh := comap_mono (f := i) hA
    change A.comap i ≤ T.comap i at hh
    rw [←hiN,comap_map_eq_self_of_injective hinj] at hh
    exact hh
  have hn₀ : N ≤ normalizer (A.comap i : Set d.overgroup) := by
    intro x hx
    have hix : i x ∈ T := hiN ▸ mem_map_of_mem i hx
    exact le_normalizer_comap i (hnA hix)
  have hq₀ : ⁅⁅replacementMoved d,A.comap i⁆,A.comap i⁆ = ⊥ := by
    apply (map_injective hinj)
    rw [map_commutator,map_commutator,hiU,hAm,hquad,Subgroup.map_bot]
  have hh := map_mono (f := i) (normalizer_quadratic_le_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb _ hA₀ hn₀ hq₀)
  rwa [hAm,SmallMover.join_map i hinj,hiU,hiQ,hiN] at hh

include e hz hn in
/-- The maximum small mover acts quadratically on the whole moved cover. -/
theorem normalizer_small_mover_quadratic_knownSimple
    (hb : 4 < replacementDistance h d) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4
    ⁅⁅replacementMoved d,J⁆,J⁆ = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨u,_,_,hJ,himage,_⟩ := SylowSmallMovers.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  dsimp only
  rw [hJ]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (cube_actor_commutator_fixed s _ u himage.le)

include e hz hn in
/-- Quadraticity of the maximum small mover on every literal edge. -/
theorem edge_small_mover_quadratic_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  have hiN : N.map i = normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hh := congrArg (Subgroup.map i) (normalizer_small_mover_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hb)
  dsimp only at hh ⊢
  rw [map_commutator,map_commutator,SmallMover.join_map i hinj,hiU,hiQ,hiN,Subgroup.map_bot] at hh
  exact hh

include e hz hn in
/-- In the order-sixteen branch the source small mover is a normal index-two
subgroup of the actual edge core, with eight images and quadratic full-cover action. -/
theorem sixteen_edge_small_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    Q d.radical a ≤ J ∧ J ≤ Q d.radical t ∧
      (Q d.radical a).relIndex J = 8 ∧ J.relIndex (Q d.radical t) = 2 ∧
      Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := by
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard ha hat
  obtain ⟨J,_,hj,hQJ,hJT,hQidx,hidx,_,_⟩ :=
    SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
  dsimp only at hj hJT hidx ⊢
  rw [hT] at hj hJT hidx
  rw [hj]
  refine ⟨hQJ,hJT,hQidx,hidx,?_,?_⟩
  · exact (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hidx)
  · have hh := edge_small_mover_quadratic_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
    dsimp only at hh
    rwa [hT,hj] at hh

include e hz hn in
/-- Unequal neighboring small movers generate the entire order-sixteen edge
core. Their intersection has index four, and each acts nonquadratically on
the other's whole moved cover. This is the opening comparison in MS93 (5.5). -/
theorem sixteen_unequal_neighbor_movers_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    J ⊔ E = Q d.radical t ∧ (J ⊓ E).relIndex (Q d.radical t) = 4 ∧
      ⁅⁅U d.radical a,E⁆,E⁆ ≠ ⊥ ∧ ⁅⁅U d.radical c,J⁆,J⁆ ≠ ⊥ := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  obtain ⟨_,hJT,_,hJi,hJn,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  obtain ⟨_,hET,_,hEi,hEn,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 a (adjacent_symm d.radical hat))) (inclusion_injective _)
  have hpair := SylowKernelPair.two_hyperplanes (Q d.radical t) J E hJT hET hJi hEi hne.symm
  have control (x : Vertex d.radical) (hx : color d.radical x = false)
      (hxt : Adjacent d.radical x t) (A : Subgroup (FreeAmalgam d.radical))
      (hAT : A ≤ Q d.radical t) (hAn : Q d.radical t ≤ normalizer (A : Set _))
      (hAi : A.relIndex (Q d.radical t) = 2)
      (hquad : ⁅⁅U d.radical x,A⁆,A⁆ = ⊥) :
      A = SmallMover.join (U d.radical x) (Q d.radical x) (Q d.radical t) 4 := by
    have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard hx hxt
    have hh := edge_normalizer_quadratic_le_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hx hxt A (hT.symm ▸ hAT) (hT.symm ▸ hAn) hquad
    rw [hT] at hh
    obtain ⟨_,hBT,_,hBi,_⟩ := sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard hx hxt
    have hi := relIndex_mul_relIndex A _ (Q d.radical t) hh hBT
    rw [hAi,hBi] at hi
    exact le_antisymm hh (relIndex_eq_one.mp (by omega))
  exact ⟨hpair.1,hpair.2,
    fun hq => hne (control a ha hat E hET hEn hEi hq),
    fun hq => hne (control c hc hct J hJT hJn hJi hq).symm⟩

include e hz hn in
/-- On the actual critical path, an unequal neighboring small mover moves
the critical line whenever the full edge core does. The transporter is
chosen inside that neighboring mover and keeps the literal first edge. -/
theorem sixteen_unequal_neighbor_moves_line_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hct : Adjacent d.radical c (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ x ∈ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4,
      x ∈ Q d.radical (p.walk.getVert 1) ∧
      x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∉ normalizer ((Z d.radical a ⊓ Q d.radical a' :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  classical
  let t := p.walk.getVert 1
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hpair := sixteen_unequal_neighbor_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hk := SylowSmallMovers.small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hk
  rw [hT] at hk
  have hEC : ¬ E ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hmove (hpair.1 ▸ sup_le hk.2.1 hh)
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hEC
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  refine ⟨x,hx,hET hx,hxc,?_⟩
  intro hxn
  have hJx : x ∈ J := by
    change x ∈ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    rw [← hk.2.2.2 hmove]
    exact ⟨hET hx, hxn⟩
  exact hxc (hk.2.1 hJx)


include e hz hn in
/-- An unequal neighboring mover has at least eight images modulo the
starting core and fixes a subgroup of index greater than four in the full
starting cover. No containment of the starting core in the neighbor is assumed. -/
theorem sixteen_unequal_neighbor_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    8 ≤ (Q d.radical a).relIndex E ∧
      4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
  let S₀ := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S₀
  let Q₀ := (Q d.radical a).subgroupOf S₀
  let T₀ := (Q d.radical t).subgroupOf S₀
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let J₀ := J.subgroupOf S₀
  let E₀ := E.subgroupOf S₀
  let := finite_stabilizer d.radical a
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  obtain ⟨hQJ,hJT,hQi,hJi,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  obtain ⟨_,hET,_,hEi,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  have hUS : U d.radical a ≤ S₀ := (DistanceEight.U_le_Z d.radical a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S₀ := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S₀ := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S₀ := hJT.trans hTS
  have hES : E ≤ S₀ := hET.trans hTS
  have hjoin : SmallMover.join U₀ Q₀ T₀ 4 = J₀ := by
    apply map_injective S₀.subtype_injective
    rw [SmallMover.join_map S₀.subtype S₀.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hQS,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hJS]
  have hcard' : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S₀.subtype_injective (K := J₀),
      ←card_map_of_injective S₀.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    have hj := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) J (Q d.radical t) bot_le hJT
    have he := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) E (Q d.radical t) bot_le hET
    rw [relIndex_bot_left,relIndex_bot_left,hJi] at hj
    rw [relIndex_bot_left,relIndex_bot_left,hEi] at he
    omega
  have hlarge : Q₀.relIndex J₀ = 8 := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm.trans hQi
  have hEl : 8 ≤ Q₀.relIndex E₀ := by
    rw [←hlarge]
    exact SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀ (comap_mono hQJ) hcard'
  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective Q₀ E₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    rwa [hh]
  · by_contra hnidx
    have hi : (centralizer (E₀ : Set S₀)).relIndex U₀ ≤ 4 := by
      have hh := SmallMover.centralizer_index_map S₀.subtype S₀.subtype_injective U₀ E₀
      rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
      rw [←hh]
      exact le_of_not_gt hnidx
    have he := SmallMover.eq_join_of_card_eq_of_index_le U₀ Q₀ T₀ 4 (by decide)
      (hjoin.symm ▸ comap_mono hQJ) (by rw [hjoin,hlarge]; decide)
      E₀ (comap_mono hET) (hjoin.symm ▸ hcard') hi
    rw [hjoin] at he
    have hh := congrArg (Subgroup.map S₀.subtype) he
    rw [map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hJS] at hh
    exact hne hh

include e hz hn in
/-- The unequal mover at the second vertex supplies a literal new critical
path with the same first three vertices. Its two full critical kernels
span the starting seed and have invariant intersection of index four. -/
theorem sixteen_second_mover_critical_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ x ∈ SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4,
      x ∈ Q d.radical (p.walk.getVert 1) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x⁻¹ a'),
        (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
        (Q d.radical (act d.radical x⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
        let K := Z d.radical a ⊓ Q d.radical a'
        let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
        K ⊔ K' = Z d.radical a ∧ (K ⊓ K').relIndex (Z d.radical a) = 4 ∧
          Q d.radical (p.walk.getVert 1) ≤ normalizer ((K ⊓ K' :
            Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          (Q d.radical a ⊔ Z d.radical a') ⊓
            (Q d.radical a ⊔ Z d.radical (act d.radical x⁻¹ a')) = Q d.radical a := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt,hxc,_⟩ := sixteen_unequal_neighbor_moves_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hct hne hmove
  have hxT : x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := ⟨(Q d.radical _).le_normalizer hxt,
        hxt.2 a (adjacent_symm d.radical hat)⟩
  obtain ⟨q,hq,_,hi,hjoin,hidx,hnorm,hcore⟩ := SylowKernelPair.small_moving_kernel_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x hxT hxc
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  rw [hT] at hnorm
  refine ⟨x,hx,hxt,q,hq,?_,?_,hi,hjoin,hidx,hnorm,hcore⟩
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 1)).inv_mem hxt.1
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 2)).inv_mem
      (hxt.2 _ (adjacent_symm d.radical hct))


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
