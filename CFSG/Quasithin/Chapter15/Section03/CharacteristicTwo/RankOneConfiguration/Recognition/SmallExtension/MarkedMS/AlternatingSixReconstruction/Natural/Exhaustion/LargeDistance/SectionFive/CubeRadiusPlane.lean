module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EndpointAttachment

/-!
# The source radius commutator modulo its full center

In the three-pair branch the whole incident edge commutator has central
index four. This follows from the natural displacement formula and fixed
codimension two of the three-pair group. The full vertex seed has the same
commutator as its moved cover, since its edge attachment centralizes every
actor in that edge kernel. Transport uses the original vertex embedding.

An edge actor with image order greater than two therefore has exactly the
same commutator modulo the entire central seed as the full edge kernel.
Its commutator has order four or eight: the natural quotient has order four
and the retained moving central kernel has order at most two. No deletion
of the central line in the order-thirty-two cover is made.

Apply this to the literal H = [Z_(a-2), V_(a'-2) intersect Q_a] of (5.11).
The previously established displacement inequalities identify H modulo the
central seed with the full backward edge commutator. H lies in the actual
backward edge seed, in Z_a and in V_(a'-2), and centralizes V_a'. Both
strict radius bounds and intermediate centrality remain explicit in this
application. In particular, central index four is not the source's missing
upper bound of two. Strict radius growth, that upper bound and the final
large-distance exclusions remain unproved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the H comparison in (5.11)(2), printed p.924, and the six-letter
module calculations of (3.3), pp.866--867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


/-- The full radical commutator has order four modulo the ambient center. -/
theorem cube_cover_commutator_central_index (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom) :
    (center d.overgroup).relIndex ⁅replacementMoved d,d.radical⁆ = 4 := by
  rw [cover_commutator_central_index s,hfull,fixedCodim_map_conj]
  rw [CFSG.Quasithin.ChapterB.Offenders.Six.fixedCodim_D.2.2.2]
  rfl

include h e hz in
private theorem seed_commutator_eq_moving
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical t) :
    ⁅Z d.radical a,A⁆ = ⁅U d.radical a,A⁆ := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hA hy)
  have hN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx y hy
  have hx' : x ∈ (U d.radical a : Set (FreeAmalgam d.radical)) *
      (Z d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hx
  obtain ⟨v,hv,z,hz,rfl⟩ := hx'
  have he : ⁅z,y⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz y hy).symm
  rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hv hy

include s in
/-- The full edge commutator has central index four at every original vertex. -/
theorem cube_graph_edge_commutator_central_index
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical a,Q d.radical t⁆ = 4 := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · have he := stabilizer_act d.radical g (alpha d.radical)
        simpa only [i,alpha,act_mVertex,one_mul,stabilizer_m_base,Mbar,MonoidHom.range_comp] using he.symm
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
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
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
  rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) ha hat _ le_rfl,
    ←hiU,←hiR,←map_commutator,←relIndex_comap,hC]
  exact cube_cover_commutator_central_index s u hfull


private theorem central_completion_of_index_four {F : Type*} [Group F]
    (P C H J : Subgroup F) [Finite C] [Finite H] [Finite J] (hHP : H ≤ P) (hJP : J ≤ P) (hHJ : H ≤ J)
    (hC : C ≤ centralizer (P : Set F))
    (hH : C.relIndex H=4) (hJ : C.relIndex J=4) :
    H ⊔ C = J ⊔ C := by
  have hCH : C ≤ normalizer (H : Set F) :=
    (hC.trans (centralizer_le hHP)).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ : C ≤ normalizer (J : Set F) :=
    (hC.trans (centralizer_le hJP)).trans (Subgroup.centralizer_le_normalizer _)
  have hmono : H ⊔ C ≤ J ⊔ C := sup_le_sup_right hHJ C
  have ht := relIndex_mul_relIndex C (H ⊔ C) (J ⊔ C) le_sup_right hmono
  rw [relIndex_sup_of_normalizes _ _ hCH,relIndex_sup_of_normalizes _ _ hCJ,hH,hJ] at ht
  have hindex : (H ⊔ C).relIndex (J ⊔ C)=1 := by omega
  exact le_antisymm hmono (relIndex_eq_one.mp hindex)

include s in
/-- A large edge actor fills the full edge commutator modulo the central seed.
The full commutator has order four or eight, retaining both covers. -/
theorem cube_graph_large_actor_commutator_plane
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical t) (hlarge : 2 < (Q d.radical a).relIndex A) :
    let C := Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
    (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical a,A⁆ = 4 ∧
      (Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) = 4 ∨
        Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) = 8) ∧
      ⁅Z d.radical a,A⁆ ⊔ C = ⁅Z d.radical a,Q d.radical t⁆ ⊔ C := by
  let C := Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let H := ⁅Z d.radical a,A⁆
  let J := ⁅Z d.radical a,Q d.radical t⁆
  have hQG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hJG : J ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hQG.trans (Z_normalized d.radical a))
  have hHJ : H ≤ J := commutator_mono le_rfl hA
  have hHZ : H ≤ Z d.radical a := hHJ.trans hJG
  let := finite_Z d.radical a
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  have hupper := cube_graph_edge_commutator_central_index s hc u hfull ha hat
  have hlower := graph_large_actor_seed_commutator_index s hc ha A (hA.trans hQG) hlarge
  have hmono := relIndex_le_of_le_right
    (H := centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    hHJ index_ne_zero_of_finite
  have hexact : (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex H=4 := by
    change (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex J=4 at hupper
    exact Nat.le_antisymm (hmono.trans_eq hupper) hlower
  have hHU : H ≤ U d.radical a := by
    change ⁅Z d.radical a,A⁆ ≤ _
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) ha hat A hA]
    exact le_normalizer_iff_commutator_le_left.mp ((hA.trans hQG).trans (U_normalized a))
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let CZ := centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let : Finite (U d.radical a ⊓ CZ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite (H ⊓ CZ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hcent : Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le (inf_le_inf_right CZ hHU)).trans (moving_central_attachment_card s hc ha)
  have hpos : 0 < Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam d.radical)) :=
    Nat.card_pos
  have hsize := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
    (H ⊓ CZ) H bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hsize
  change Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam d.radical)) *
    (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex H =
      Nat.card H at hsize
  rw [hexact] at hsize
  have horder : Nat.card H=4 ∨ Nat.card H=8 := by omega
  have hidx (K : Subgroup (FreeAmalgam d.radical)) (hK : K ≤ Z d.radical a) :
      C.relIndex K =
        (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex K := by
    change (C.subgroupOf K).index = _
    congr 1
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hK x.property,hx⟩⟩
  refine ⟨hexact,horder,central_completion_of_index_four (Z d.radical a) C H J hHZ hJG hHJ ?_ ?_ ?_⟩
  · exact inf_le_right.trans (centralizer_le (Z_le_stabilizer d.radical a))
  · rw [hidx H hHZ]; exact hexact
  · rw [hidx J hJG]; exact hupper

include e hz hn in
/-- The source H fills the same natural commutator plane as the whole
backward edge kernel. Both strict radius premises remain explicit. -/
theorem nonsylow_intermediate_central_radius_plane_knownSimple
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
    let C := Z d.radical q.start ⊓
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))
    (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H = 4 ∧
      (Nat.card H = 4 ∨ Nat.card H = 8) ∧
      H ⊔ C = ⁅Z d.radical q.start,Q d.radical q.edge⁆ ⊔ C ∧
      H ≤ Z d.radical q.edge ∧ H ≤ Z d.radical a ∧
      H ≤ V d.radical (p.walk.getVert (p.walk.length-2)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
  let A := V d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical a
  let H := ⁅Z d.radical q.start,A⁆
  obtain ⟨_,hlarge,_,hHZ,hHV,hfixed⟩ :=
    nonsylow_intermediate_central_radius_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p q r hcentral hstrict₀ hstrict
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hns
  have hR : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hA : A ≤ Q d.radical q.edge :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht q.adjacent_start)
  have hplane := cube_graph_large_actor_commutator_plane s hc u hR
    q.path.start_color q.adjacent_shift A hA hlarge
  exact ⟨hplane.1,hplane.2.1,hplane.2.2,(commutator_mono le_rfl hA).trans
    (cube_edge_seed_commutator_le s hc u hR.le q.path.start_color q.adjacent_shift),hHZ,hHV,hfixed⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
