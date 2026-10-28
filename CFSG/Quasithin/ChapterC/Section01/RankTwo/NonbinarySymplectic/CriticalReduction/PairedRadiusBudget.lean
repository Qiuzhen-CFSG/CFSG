module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusKernels
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.MovingRadius

/-!
# The literal q-squared radius budget in MS93 (5.11)

The critical endpoint cannot fix the radius modulo its original seed:
its escaping action would force the entire radius into the full fixed
preimage B, contradicting the strict moving index. Thus the radius is
strictly larger than the starting seed joined with its full endpoint
kernel. At distance greater than four, commutativity factors the literal
relative index through this join, without assuming that the radius fixes
the endpoint.

Consequently a radius index at most q squared forces both original
critical images to have order q and leaves a nontrivial factor at most q.
The full endpoint kernel still has index at least q squared modulo B.
On the same paired source selection, the joined seeds have index at most
q modulo the original seed joined with Q; the previously proved paired
image/kernel obstruction is retained on that very conjugator.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the first contradiction in (5.11), printed p.923. This does not
identify the original seed-kernel product with the penultimate kernel.
The two literal premises of the paired obstruction, the strict q-squared
radius bound, the remaining (5.11)--(5.12) exclusions, and the actual
minimum-replacement distance-two witness remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The escaping critical endpoint acts nontrivially on the complete
radius modulo its starting seed. -/
theorem Input.replacement_radius_endpoint_displacement_not_le_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    ¬ ⁅V d.radical a,Z d.radical z⁆ ≤ Z d.radical a := by
  intro hdisp
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hescape := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; exact (by omega : 0 < geometry.b d.radical))
    z path.end_color path.critical).2
  have hVB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color
    f hf hk (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color)
    (V d.radical a) (Z d.radical z) le_rfl (DistanceEight.V_normalized d.radical a)
    (path.endpoint_Z_le_start_stabilizer (by omega)) hescape hdisp
  have hUV : U d.radical (path.walk.getVert 2) ≤ V d.radical a :=
    (U_le_Z _).trans (le_iSup_of_le _ (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm]
      exact (path.dist_start (by rw [path.length_eq_b]; omega : 2 ≤ path.walk.length)).le) le_rfl))
  have hone := relIndex_eq_one.mpr (hUV.trans hVB)
  have hstrict := h.replacement_path_moving_index_gt_field d path hb
  rw [hone] at hstrict
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

omit h in
private theorem relative_index_factor_of_commutative {G : Type*} [Group G]
    (V Z Q : Subgroup G) [IsMulCommutative V] (hZ : Z ≤ V) :
    Q.relIndex Z * (Z ⊔ (V ⊓ Q)).relIndex V = Q.relIndex V := by
  let W := V ⊓ Q
  have hW : W ≤ V := inf_le_left
  let : CommGroup V := IsMulCommutative.instCommGroup
  have hi := relIndex_sup_right (Z.subgroupOf V) (W.subgroupOf V)
  rw [←subgroupOf_sup hZ hW,relIndex_subgroupOf (sup_le hZ hW),
    relIndex_subgroupOf hZ] at hi
  have hZW : (V ⊓ Q).relIndex Z = Q.relIndex Z := by
    change ((V ⊓ Q).subgroupOf Z).index=(Q.subgroupOf Z).index
    congr 1
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hZ x.property,hx⟩⟩
  have hh := relIndex_mul_relIndex W (Z ⊔ W) V le_sup_right (sup_le hZ hW)
  rw [hi,hZW,inf_relIndex_left] at hh
  exact hh

/-- The original seed and full endpoint kernel do not cover the radius.
In particular endpoint-stabilizer containment is not an input. -/
theorem Input.replacement_radius_seed_kernel_not_cover
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    ¬ V d.radical a ≤ Z d.radical a ⊔ Q d.radical z := by
  intro hcover
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hAQ := hAS.trans (Q_normalized d.radical z)
  have hQC : Q d.radical z ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z path.end_color))
  apply h.replacement_radius_endpoint_displacement_not_le_seed d path hb
  apply commutator_le.mpr
  intro v hv y hy
  have hv' : v ∈ (Z d.radical a : Set (FreeAmalgam d.radical))*(Q d.radical z : Set _) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hAQ]
    exact hcover hv
  obtain ⟨u,hu,k,hk,rfl⟩ := hv'
  have hcomm : ⁅k,y⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hQC hk y hy).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hcomm,mul_one,mul_inv_cancel,one_mul]
  exact critical_commutator_le_start_seed path (commutator_mem_commutator hu hy)

/-- The actual seed-kernel join leaves a nontrivial radius quotient. -/
theorem Input.replacement_radius_seed_kernel_index_gt_one
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    1 < (Z d.radical a ⊔ (V d.radical a ⊓ Q d.radical z)).relIndex (V d.radical a) := by
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  have hpos : 0 < (Z d.radical a ⊔ (V d.radical a ⊓ Q d.radical z)).relIndex (V d.radical a) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : (Z d.radical a ⊔ (V d.radical a ⊓ Q d.radical z)).relIndex (V d.radical a) ≠ 1 := by
    intro he
    exact h.replacement_radius_seed_kernel_not_cover d path hb
      ((relIndex_eq_one.mp he).trans (sup_le_sup_left inf_le_right _))
  omega

/-- A q-squared radius budget forces field-sized critical images in both
directions and leaves a strict factor at most q after the full seed-kernel
join. All indices are taken in the original infinite amalgam. -/
theorem Input.replacement_small_radius_critical_indices
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z)=Nat.card F ∧
      1 < (Z d.radical a ⊔ (V d.radical a ⊓ Q d.radical z)).relIndex (V d.radical a) ∧
      (Z d.radical a ⊔ (V d.radical a ⊓ Q d.radical z)).relIndex (V d.radical a) ≤ Nat.card F := by
  let := V_abelian_of_four_lt d.radical path.start_color hb
  have hprod := relative_index_factor_of_commutative (V d.radical a) (Z d.radical a)
    (Q d.radical z) (Z_le_VBall d.radical a 2)
  have hgt := h.replacement_radius_seed_kernel_index_gt_one d path hb
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical z).relIndex (Z d.radical a)<Nat.card F^2 := by
    nlinarith
  obtain ⟨hz,ha⟩ := h.replacement_small_critical_indices_eq_field d path (by omega) hsmall
  refine ⟨hz,ha,hgt,?_⟩
  rw [hz] at hprod
  nlinarith

/-- The complete endpoint kernel keeps at least two field dimensions modulo
B under the small-radius hypothesis. -/
theorem Input.replacement_small_radius_full_kernel_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    Nat.card F^2 ≤ (B d.radical a (geometry.Z_normal a)).relIndex
      (V d.radical a ⊓ Q d.radical z) := by
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hlo := h.replacement_moving_radius_index_ge_fourth_power d geometry
    (by omega) path.start_color hat
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  let D := B d.radical a (geometry.Z_normal a)
  have hmon : D.relIndex (V d.radical a) ≤ (D ⊓ Q d.radical z).relIndex (V d.radical a) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hprod := relIndex_inf_mul_relIndex D (Q d.radical z) (V d.radical a)
  rw [inf_comm (Q d.radical z) (V d.radical a)] at hprod
  have hm := Nat.mul_le_mul_left (D.relIndex (V d.radical a ⊓ Q d.radical z)) hi
  rw [hprod] at hm
  have hl := hlo.trans (hmon.trans hm)
  have hq : 0 < Nat.card F^2 := pow_pos Nat.card_pos _
  nlinarith [show Nat.card F^4=(Nat.card F^2)^2 by ring]

/-- On the very same paired backward path, the original q-squared bound
leaves a field-sized critical image and a strict remaining index. In
particular the entire paired seed join has index at most q modulo the
original seed joined with its full endpoint kernel. -/
theorem Input.replacement_paired_radius_original_budget
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2) :
    ∃ x ∈ Ltilde d.radical p.first,
      let Y := Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first)
      (Z d.radical p.first ⊔ Q d.radical p.last).relIndex Y ≤ Nat.card F ∧
      (Q d.radical p.last).relIndex (Z d.radical p.first)=Nat.card F ∧
      (Q d.radical p.first).relIndex (Z d.radical p.last)=Nat.card F ∧
      (Nat.card F < (Q d.radical p'.last).relIndex Y ∨
        ¬ Y ⊓ Q d.radical p'.last ≤ Z d.radical p.first ⊔ Q d.radical p.last) := by
  obtain ⟨x,hx,hobstruction⟩ := h.replacement_paired_radius_image_kernel_obstruction d p p' hb hl
  refine ⟨x,hx,?_⟩
  dsimp only at hobstruction ⊢
  obtain ⟨hz,ha,_,hbudget⟩ := h.replacement_small_radius_critical_indices d p.path hb hi
  refine ⟨?_,hz,ha,hobstruction⟩
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  have hax : act d.radical x p.first=p.first := Ltilde_le_stabilizer _ hx
  have hatx : Adjacent d.radical p.first (act d.radical x t) := by
    rw [←hax]
    exact (adjacent_act_iff d.radical x p.first t).mpr hat
  have hvtx : Adjacent d.radical (act d.radical x p'.first) (act d.radical x t) :=
    (adjacent_act_iff d.radical x p'.first t).mpr hvt
  have hYV : Z d.radical p'.first ⊔ Z d.radical (act d.radical x p'.first) ≤ V d.radical p.first :=
    sup_le (le_sup_left.trans (neighbor_seed_join_le_radius hat hvt))
      (le_sup_left.trans (neighbor_seed_join_le_radius hatx hvtx))
  let := finite_stabilizer d.radical p.first
  let : Finite (V d.radical p.first) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) p.first p.path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  have hsmall : (Z d.radical p.first ⊔ Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F :=
    (relIndex_le_of_le_left (sup_le_sup_left inf_le_right _) index_ne_zero_of_finite).trans hbudget
  exact (relIndex_le_of_le_right hYV index_ne_zero_of_finite).trans hsmall

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
