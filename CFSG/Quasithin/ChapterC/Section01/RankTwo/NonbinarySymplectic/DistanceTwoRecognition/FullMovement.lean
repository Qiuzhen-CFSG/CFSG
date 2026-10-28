module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.KernelGeometry
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.RootFixed
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Sections
public import Theory.Representation.BinaryConjugationSection.CommutatorFixedExtension

/-!
# Full movement of the actual secondary quotient

The original opposite-kernel action is a point radical. Its displacement
hyperplane is the fixed space of the critical root. Every element of the
opposite Z-kernel intersection therefore lifts from natural displacement;
the difference lies in the full cover kernel, already contained in the
common edge center. This proves the required group containment without
choosing a complement to any fixed attachment.

Full inner action then puts this displacement in the intrinsic core times
Z. The maximal secondary seed generates its actual orbit A, so A = core Z.
Under the literal secondary quotient coordinates this says that A/Z is fully
moved by the component. It does not assert that the fixed kernel in A is
trivial. The paired-orbit contradiction remains a further source step.

Source: MS93 (3.6), printed p.871, immediately before the orthogonal-cover
and paired Frattini argument.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource Sp4Four.CoreReconstruction
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem opposite_Z_decomposition
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Z d.radical z = U d.radical z ⊔ Z d.radical t := by
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g
        (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
          (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
        a path.start_color (by
          rw [g.distance_constant a path.start_color]
          change 0 < g.b d.radical
          omega) z path.end_color path.critical }
  have hl : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge)) path.end_color
  exact replacement_nonfrattini_Z_eq_moving_sup_edge h d rev hb hzt hl

omit h in
private theorem intersection_displacement_of_cover
    {M J W : Type*} [Group M] [Finite M] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {B₀ : Subgroup J}
    {T : Subgroup M} {g : Geometry T} {a z t : Vertex T} {n : ℕ}
    (path : CriticalPath T g a z) (hpos : 0 < g.b T)
    (hat : Adjacent T a t) (hzt : Adjacent T z t)
    (s : MovedSection ρ B₀) (cv : KernelPointCover T s n a z)
    (hdecomp : Z T z = U T z ⊔ Z T t)
    (hfixed : X T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T)) ≤ Z T t) :
    Z T z ⊓ Q T a ≤ ⁅Q T a,Z T z⁆ ⊔ Z T t := by
  let E := cv.field
  let β := cv.actor
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  let p := MovedSection.coverProjection s cv.equiv
  let j := cv.embedding
  have hZAQ : Z T a ≤ Q T a := (g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b T
    exact hpos)).trans (omegaCenter_le _)
  let B := (Z T a).subgroupOf (Q T a) |>.map α
  let := g.Z_elementary hpos a path.start_color
  let : IsElementaryAbelian 2 ((Z T a).subgroupOf (Q T a)) :=
    IsElementaryAbelian.subgroupOf hZAQ
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map α
  have hBne : B ≠ ⊥ := by
    intro he
    have hkB := (map_eq_bot_iff ((Z T a).subgroupOf (Q T a))).mp he
    apply path.critical.2
    intro x hx
    have hh := mem_map_of_mem (Q T a).subtype
      (hkB (show (⟨x,hZAQ hx⟩ : Q T a) ∈
        (Z T a).subgroupOf (Q T a) from hx))
    rw [cv.actor_kernel] at hh
    exact hh.2
  have hBr : ∀ x ∈ B, Module.finrank E.Carrier (InvolutionTypes.movedSpace x) ≤ 1 := by
    rintro _ ⟨u,hu,rfl⟩
    exact cv.root_actor u hu
  obtain ⟨c,hc⟩ := cv.point_image
  have hdisp := MaximalElementary.point_displacement_eq_root_fixed α.range B
    (map_le_range α _) hBne hBr c hc
  have hZtZa := Sp4Four.edge_Z_le_endpoint T path.start_color hat
  have hZtZz := Sp4Four.edge_Z_le_endpoint T path.end_color hzt
  let := g.Z_elementary hpos z path.end_color
  have hsplit : (U T z).subgroupOf (Z T z) ⊔
      (Z T t).subgroupOf (Z T z) = ⊤ := by
    rw [←subgroupOf_sup (U_le_Z z) hZtZz,←hdecomp]
    exact subgroupOf_self _
  intro x hx
  obtain ⟨u,hu,v,hv,he⟩ := Subgroup.mem_sup.mp
    (hsplit.symm ▸ (mem_top (⟨x,hx.1⟩ : Z T z)))
  have he' : u.val*v.val = x := congrArg Subtype.val he
  have huQ : u.val ∈ Q T a := by
    have hh := (Q T a).mul_mem hx.2 ((Q T a).inv_mem (hZAQ (hZtZa hv)))
    change x*v.val⁻¹ ∈ Q T a at hh
    rwa [←he',mul_inv_cancel_right] at hh
  obtain ⟨w,hw⟩ := (cv.range_eq.symm ▸ hu : u.val ∈ j.range)
  have hfix : p w.toAdd ∈ TwoLocalCover.fixedSpace B := by
    rintro _ ⟨b,hb,rfl⟩
    have hcomm := (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a path.start_color)) hb u.val huQ
    change u.val*b.val=b.val*u.val at hcomm
    have hh := cv.actor_conjugation b w.toAdd
    change j (Multiplicative.ofAdd (MovedSection.coverAction s cv.equiv (β b) w.toAdd)) =
      b.val*j w*b.val⁻¹ at hh
    rw [hw,←hcomm,mul_inv_cancel_right,←hw] at hh
    have hh' := congrArg p (Multiplicative.ofAdd.injective (cv.injective hh))
    rw [p.isIntertwining] at hh'
    exact hh'
  obtain ⟨w',hw',hcw⟩ := natural_displacement_lifts (U T z) (Q T a)
    j cv.range_eq β (MovedSection.coverAction s cv.equiv) cv.actor_conjugation p cv.cover.1
    (p w.toAdd) (hdisp.symm ▸ hfix)
  have hdiff : j (Multiplicative.ofAdd (w.toAdd-w')) ∈ Z T t := by
    apply hfixed
    refine ⟨?_,(cv.kernel _).mp ?_⟩
    · exact ((U_le_Z z).trans (g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]
        exact hpos))) (cv.range_eq ▸ ⟨_,rfl⟩)
    · change p (w.toAdd-w') = 0
      rw [map_sub,hw',sub_self]
  have huw : j w ∈ ⁅Q T a,Z T z⁆ ⊔ Z T t := by
    have hh := mul_mem (mem_sup_right hdiff)
      (mem_sup_left (commutator_mono le_rfl (U_le_Z z) hcw))
    simpa only [←map_mul,←ofAdd_add,sub_add_cancel,ofAdd_toAdd] using hh
  rw [←he',←hw]
  exact mul_mem huw (mem_sup_right hv)

/-- The actual opposite Z-kernel intersection lies in the whole displacement
plus the common edge center. The natural point-radical calculation is lifted
through the original projection and its complete fixed kernel. -/
theorem replacement_kernel_intersection_le_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Z d.radical z ⊓ Q d.radical a ≤ ⁅Q d.radical a,Z d.radical z⁆ ⊔ Z d.radical t := by
  obtain ⟨cv⟩ := replacement_kernel_point_cover h d path hb hat hzt hlarge
  exact intersection_displacement_of_cover path (by omega) hat hzt _ cv
    (opposite_Z_decomposition h d path hb hzt hlarge)
    (replacement_fixed_X_le_edge h d (g := g) (by omega) path.end_color hzt)

/-- Full inner action puts secondary displacement into the intrinsic core
modulo the original Z-layer. -/
theorem replacement_secondary_displacement_le_core_sup_Z
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ⁅Q d.radical a,Z d.radical z⁆ ≤ core d.radical a ⊔ Z d.radical a := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let D := core d.radical a ⊔ Z d.radical a
  have hn : stabilizer d.radical a ≤ normalizer D :=
    (le_inf (DistanceTwo.core_normalized a) (Z_normalized d.radical a)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hgen : stabilizer d.radical a ≤ Ltilde d.radical a ⊔ Q d.radical a := by
    rw [←replacement_edge_generation h d path.start_color hat]
    exact sup_le le_sup_left (replacement_inner_edge h d (g := g) (by omega) path.start_color hat)
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  rw [replacement_kernel_displacement_eq_secondary h d path hb hat hzt hlarge,commutator_comm]
  apply (commutator_mono (hzS.trans hgen) le_rfl).trans
  apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Ltilde d.radical a) (Q d.radical a) A D hn (Ltilde_le_stabilizer a) (fun _ hx => hx.1)
  · rw [commutator_comm,replacement_secondary_component_commutator_eq_core h d path hb hat hzt hlarge]
    exact le_sup_left
  · rw [commutator_comm]
    exact (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).2.1.trans le_sup_right

/-- The entire secondary quotient A/Z is fully moved. This conclusion uses
the source seed geometry with the whole cover kernel retained. -/
theorem replacement_secondary_eq_core_sup_Z
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z) =
      core d.radical a ⊔ Z d.radical a := by
  apply le_antisymm
  · apply Sp4Four.conjugatesIn_le_of_normalized
    · apply (le_inf (Sp4Four.secondarySeed_le d.radical a t z)
        (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)).trans
      apply (replacement_kernel_intersection_le_displacement h d path hb hat hzt hlarge).trans
      exact sup_le (replacement_secondary_displacement_le_core_sup_Z h d path hb hat hzt hlarge)
        ((Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat).trans le_sup_right)
    · exact (le_inf (DistanceTwo.core_normalized a) (Z_normalized d.radical a)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact sup_le (replacement_core_le_secondary_orbit h d path hb hat hzt hlarge)
      (secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt)
/-- The original secondary coordinates have no unmoved quotient: their
canonical component-commutator space is the entire representation. -/
theorem replacement_secondary_fully_moved
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    BinaryOffender.subspaceCommutator σ ⊤ (replacementComponent d) = ⊤ := by
  let := replacementComponent_normal h d
  let s := MovedSection.ofNormal σ (replacementComponent d)
  change moved σ (replacementComponent d) = ⊤
  rw [←s.space_eq,←replacement_core_secondary_image h d path hb hat hzt hlarge κ hL σ c,
    ←c.imageSpace_sup_kernel _ (replacement_core_le_secondary_orbit h d path hb hat hzt hlarge),
    ←replacement_secondary_eq_core_sup_Z h d path hb hat hzt hlarge]
  apply top_unique
  intro v _
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
  exact (c.mem_imageSpace_iff _ v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
