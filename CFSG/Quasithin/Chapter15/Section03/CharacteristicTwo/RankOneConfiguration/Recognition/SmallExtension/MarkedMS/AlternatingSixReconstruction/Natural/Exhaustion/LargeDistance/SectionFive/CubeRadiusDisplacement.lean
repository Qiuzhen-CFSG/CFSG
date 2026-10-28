module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeIntermediateLine
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalMovedSpace
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths

/-!
# Radius-actor displacement modulo the full central attachment

The natural projection of either permitted moved cover has precisely the
ambient central kernel. The image of its commutator with an arbitrary actor
is the natural module's displacement space. The symplectic pairing identifies
its dimension with fixed codimension, giving an exact index formula for the
original commutator modulo the full ambient center. An actor with image order
greater than two therefore has commutator central index at least four.
This retains the order-thirty-two cover and its central line.

Transport through the original vertex embedding gives the same bound for U
and for the full seed Z at every component vertex. Apply it to the source's
literal H = [Z_(a-2), V_(a'-2) intersect Q_a] on the paired backward chain.
Under intermediate centrality and the two strict endpoint-radius bounds, the
already proved two-element joined image and subgroup-index multiplication
make both indicated radius actors large. The resulting H has central index
at least four at a-2, lies in Z_a and V_(a'-2), and centralizes V_a'.

The two strict radius bounds remain explicit: they are not discharged by
this local comparison. The final central-intersection upper bound, strict
radius growth, greater-than-six noncentrality and original large-distance
assembly remain open. No different graph, whole point core, or split cover
is substituted.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the H comparison in (5.11)(2), printed p.924. The natural-pairing and
small-image inputs are the existing six-letter results used in (3.3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

/-- The literal cover commutator modulo the ambient center has the natural
displacement order, for both allowed cover sizes. -/
theorem cover_commutator_central_index (A : Subgroup d.overgroup) :
    (center d.overgroup).relIndex ⁅replacementMoved d,A⁆ =
      2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let f := coverProjection h e hz hn d
  let ρ := naturalRepresentation (Fin 6)
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let J := ⁅U,A⁆
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hU : subgroupSpace U U = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property trivial
  have hJ : subgroupSpace U J = subspaceCommutator (coverAction s) ⊤ (A.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker U A le_rfl,hU]
    rfl
  have hm := subspaceCommutator_map_embedding ρ (coverAction s)
    (MonoidHom.id (Equiv.Perm (Fin 6))) π (fun g v => (coverMap_equivariant s g v).symm)
    (A.map s.projection) ⊤
  rw [Subgroup.map_id,Submodule.map_top,
    LinearMap.range_eq_top.mpr (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn)),←hJ] at hm
  have hcard : Nat.card ((J.subgroupOf U).map f) =
      Nat.card ((subgroupSpace U J).map π) := by
    apply Nat.card_congr
    exact {
      toFun := fun v => ⟨v.val.toAdd,by
        obtain ⟨x,hx,he⟩ := v.property
        exact ⟨Additive.ofMul x,hx,congrArg Multiplicative.toAdd he⟩⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.val,by
        obtain ⟨x,hx,he⟩ := v.property
        exact ⟨x.toMul,hx,congrArg Multiplicative.ofAdd he⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hk : f.ker = (center d.overgroup).subgroupOf U := coverProjection_kernel_center s
  rw [←relIndex_subgroupOf (L := U) (commutator_le_left U A),←hk,relIndex_ker]
  change Nat.card ((⁅U,A⁆.subgroupOf U).map f) = _
  rw [hcard,←hm,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    NaturalPairing.moved_finrank_eq_fixedCodim]

include s in
/-- Image order greater than two forces central commutator index at least four. -/
theorem cover_large_actor_commutator_index (A : Subgroup d.overgroup)
    (hlarge : 2 < (pCore 2 d.overgroup).relIndex A) :
    4 ≤ (center d.overgroup).relIndex ⁅replacementMoved d,A⁆ := by
  have hcard : 2 < Nat.card (A.map s.projection) := by
    rwa [←s.projection_kernel,relIndex_ker] at hlarge
  have hdim : 2 ≤ fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) := by
    by_contra! hsmall
    have hne : A.map s.projection ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
      (A.map s.projection) hne (by
        change fixedCodim (naturalRepresentation (Fin 6)) _ ≤ 1
        omega)
    rw [he,Nat.card_zpowers,ht.orderOf] at hcard
    omega
  rw [cover_commutator_central_index s]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdim

include s in
/-- The same bound at every original component vertex, on its whole U-cover. -/
theorem graph_large_actor_moving_commutator_index (hc : DistanceTwo.CentralLayer d)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical a)
    (hlarge : 2 < (Q d.radical a).relIndex A) :
    4 ≤ (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅U d.radical a,A⁆ := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a ha
  have hmA : (A.comap i).map i=A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : 2 < (pCore 2 d.overgroup).relIndex (A.comap i) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hmA,hiQ]
    exact hlarge
  have hC : (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).comap i =
      center d.overgroup := by
    ext x
    constructor
    · intro hx
      apply mem_center_iff.mpr
      intro g
      apply hi
      simpa only [map_mul] using hx (i g) (hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩))
    · intro hx g hg
      obtain ⟨y,rfl⟩ := hir.symm ▸ hg
      simpa only [map_mul] using congrArg i ((mem_center_iff.mp hx) y)
  have hm : (⁅replacementMoved d,A.comap i⁆ : Subgroup d.overgroup).map i =
      ⁅U d.radical a,A⁆ := by rw [map_commutator,hiU,hmA]
  rw [←hm,←relIndex_comap,hC]
  exact cover_large_actor_commutator_index s (A.comap i) hidx

include s in
/-- Full seeds inherit the lower bound without removing their central attachments. -/
theorem graph_large_actor_seed_commutator_index (hc : DistanceTwo.CentralLayer d)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical a)
    (hlarge : 2 < (Q d.radical a).relIndex A) :
    4 ≤ (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical a,A⁆ := by
  have hJZ : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized d.radical a))
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  exact (graph_large_actor_moving_commutator_index s hc ha A hA hlarge).trans
    (relIndex_le_of_le_right (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl)
      index_ne_zero_of_finite)

include e hz hn in
/-- The exact source H and both radius actors on the original paired chain.
The strict endpoint-radius bounds remain the source premises to be proved. -/
theorem nonsylow_intermediate_central_radius_displacement_knownSimple
    (hb : 6 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)))
    (hstrict₀ : 4 < (Q d.radical a).relIndex (V d.radical a'))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2)))) :
    let A := V d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical a
    let H := ⁅Z d.radical q.start,A⁆
    2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') ∧
      2 < (Q d.radical q.start).relIndex A ∧
      4 ≤ (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H ∧
      H ≤ Z d.radical a ∧ H ≤ V d.radical (p.walk.getVert (p.walk.length-2)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
  let z := p.walk.getVert (p.walk.length-2)
  let A := V d.radical z ⊓ Q d.radical a
  let H := ⁅Z d.radical q.start,A⁆
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hjoin := nonsylow_edge_paired_intermediate_central_radius_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q r hcentral
  have hi : (Q d.radical a).relIndex (V d.radical z) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q d.radical a)
      (show V d.radical z ≤ V d.radical z ⊔
        (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) from le_sup_left)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hi₀ : (Q d.radical a).relIndex
      (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q d.radical a)
      (show V d.radical a' ⊓ Q d.radical (p.walk.getVert 2) ≤ V d.radical z ⊔
        (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) from le_sup_right)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hlarge₀ : 2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') := by
    have hVQ₀ : V d.radical a' ≤ Q d.radical a' :=
      V_le_Q d.radical (geometry := replacementGeometry h d) p.end_color
        (by change 2 < replacementDistance h d; omega)
    let := finite_stabilizer d.radical a'
    let : Finite (V d.radical a') := Finite.of_injective
      (inclusion (hVQ₀.trans (fun _ hx => hx.1))) (inclusion_injective _)
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q d.radical a)
      (Q d.radical (p.walk.getVert 2)) (V d.radical a')
    rw [inf_comm (Q d.radical (p.walk.getVert 2))] at htower
    have hmono : (Q d.radical a).relIndex (V d.radical a') ≤
        (Q d.radical a ⊓ Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hi₀ hsmall)
    omega
  have hVQ : V d.radical z ≤ Q d.radical z :=
    V_le_Q d.radical (geometry := replacementGeometry h d) q.path.end_color
      (by change 2 < replacementDistance h d; omega)
  let := finite_stabilizer d.radical z
  let : Finite (V d.radical z) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hlarge : 2 < (Q d.radical q.start).relIndex A := by
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q d.radical q.start) (Q d.radical a) (V d.radical z)
    rw [inf_comm (Q d.radical a)] at htower
    have hmono : (Q d.radical q.start).relIndex (V d.radical z) ≤
        (Q d.radical q.start ⊓ Q d.radical a).relIndex (V d.radical z) :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hsmall hi)
    change 4 < (Q d.radical q.start).relIndex (V d.radical z) at hstrict
    omega
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hAedge : A ≤ Q d.radical q.edge :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht q.adjacent_start)
  have hAG : A ≤ stabilizer d.radical q.start :=
    hAedge.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_shift))
  have hlower := graph_large_actor_seed_commutator_index s hc q.path.start_color A hAG hlarge
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hns
  have hR : d.radical.map s.projection ≤
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hHZ : H ≤ Z d.radical a :=
    ((commutator_mono le_rfl hAedge).trans
      (cube_edge_seed_commutator_le s hc u hR q.path.start_color q.adjacent_shift)).trans
        (adjacent_Z_le d.radical p.start_color q.adjacent_start)
  have hZG : Z d.radical q.start ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le
  have hHV : H ≤ V d.radical z :=
    (commutator_mono le_rfl (show A ≤ V d.radical z from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (hZG.trans (DistanceEight.V_normalized d.radical z)))
  have hdist : (cosetGraph d.radical).dist z a'=2 := by
    change (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a'=2
    rw [p.dist_end]
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    omega
  have hVV : V d.radical z ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply Escape.PairingControl.Geometry.V_centralizes_V_of_distance
      (geometry := replacementGeometry h d) q.path.end_color p.end_color
    change (cosetGraph d.radical).dist z a'+4 < replacementDistance h d
    omega
  exact ⟨hlarge₀,hlarge,hlower,hHZ,hHV,hHV.trans hVV⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
