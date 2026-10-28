module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FullMovement
public import Theory.Representation.SymplecticFourOrthogonalCover.PointHyperplaneDisjoint
/-!
# Disjointness of the paired secondary seed commutators

The original point-radical cover identifies the natural displacement hyperplane
with the critical root's fixed space. Splitting Z_z as U_z Z_t retains the
entire fixed attachment in the common edge center. Its kernel-intersection
commutator consequently avoids the full component centralizer at z. The
opposite seed commutator is in that centralizer, so the paired seed commutators
and their ambient Frattini subgroups are disjoint.

The full preimage of the fixed part of A/Z centralizes A: the three-subgroups
lemma uses [A,Q] fixed by the component and A = [A,L] Z. No fixed subgroup is
removed or assumed trivial.

Source: MS93 (3.6), printed p.871, the paired Frattini and fixed-preimage step.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource Sp4Four.CoreReconstruction

private theorem intersection_commutator_disjoint_of_cover
    {M J W : Type*} [Group M] [Finite M] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {B₀ : Subgroup J}
    {T : Subgroup M} {g : Geometry T} {a z t : Vertex T} {n : ℕ}
    (path : CriticalPath T g a z) (hpos : 0 < g.b T)
    (hat : Adjacent T a t) (hzt : Adjacent T z t)
    (s : MovedSection ρ B₀) (cv : KernelPointCover T s n a z)
    (hdecomp : Z T z = U T z ⊔ Z T t) :
    Disjoint ⁅Z T z ⊓ Q T a,Q T a⁆
      (centralizer (Ltilde T z : Set (FreeAmalgam T))) := by
  let : Finite (stabilizer T z) := finite_stabilizer T z
  let : Finite (U T z) := Finite.of_injective (inclusion ((U_le_Z z).trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      exact hpos)).trans ((omegaCenter_le _).trans (fun _ hx => hx.1))))) (inclusion_injective _)
  let : Finite s.space.toSubmodule := Finite.of_injective
    (fun w => (⟨cv.embedding (Multiplicative.ofAdd w),cv.range_eq ▸ ⟨_,rfl⟩⟩ : U T z))
    (fun _ _ he => Multiplicative.ofAdd.injective (cv.injective (congrArg Subtype.val he)))
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
  let σ := MovedSection.coverAction s cv.equiv
  let P := ((displacementSpace α.range).restrictScalars (ZMod 2)).comap p.toLinearMap
  let D := subspaceCommutator σ P β.range
  let E₀ := D.toAddSubgroup.toSubgroup.map j
  have hα : β.range.map (commutator (Sp E.Carrier)).subtype = α.range := by
    rw [←MonoidHom.range_comp]
  have hD : Disjoint D (OneCohomology.fixed σ) := by
    have hh := point_hyperplane_commutator_disjoint p cv.cover β.range c (by rwa [hα])
    change Disjoint (subspaceCommutator σ
      ((displacementSpace (β.range.map (commutator (Sp E.Carrier)).subtype)).restrictScalars
        (ZMod 2) |>.comap p.toLinearMap) β.range) (OneCohomology.fixed σ) at hh
    rw [hα] at hh
    exact hh
  have hZtZa := Sp4Four.edge_Z_le_endpoint T path.start_color hat
  have hZtZz := Sp4Four.edge_Z_le_endpoint T path.end_color hzt
  let := g.Z_elementary hpos z path.end_color
  have hsplit : (U T z).subgroupOf (Z T z) ⊔
      (Z T t).subgroupOf (Z T z) = ⊤ := by
    rw [←subgroupOf_sup (U_le_Z z) hZtZz,←hdecomp]
    exact subgroupOf_self _
  have hbound : ⁅Q T a,Z T z ⊓ Q T a⁆ ≤ E₀ := by
    apply commutator_le.mpr
    intro b hb x hx
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
      change j (Multiplicative.ofAdd (σ (β b) w.toAdd)) =
        b.val*j w*b.val⁻¹ at hh
      rw [hw,←hcomm,mul_inv_cancel_right,←hw] at hh
      have hh' := congrArg p (Multiplicative.ofAdd.injective (cv.injective hh))
      rw [p.isIntertwining] at hh'
      exact hh'
    have hwP : w.toAdd ∈ P := by
      change p w.toAdd ∈ displacementSpace α.range
      rwa [hdisp]
    have hvcomm : ⁅b,v.val⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact ((commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q T a path.start_color)) (hZtZa hv) b hb)
    rw [←he',commutatorElement_mul_right_eq_mul_conj,hvcomm]
    simp only [mul_one,mul_inv_cancel_right]
    refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd),?_,?_⟩
    · change σ (β ⟨b,hb⟩) w.toAdd-w.toAdd ∈ D
      exact Submodule.subset_span ⟨β ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩,w.toAdd,hwP,rfl⟩
    · rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,cv.actor_conjugation]
      change b*j w*b⁻¹*(j w)⁻¹=⁅b,u.val⁆
      rw [hw]
      rfl
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxE := hbound ((commutator_comm (Z T z ⊓ Q T a) (Q T a)) ▸ hx.1)
  obtain ⟨w,hw,rfl⟩ := hxE
  have hwker : p w.toAdd = 0 := (cv.kernel w.toAdd).mpr hx.2
  have hwfixed : w.toAdd ∈ OneCohomology.fixed σ := (cover_fixed_kernel p cv.cover).ge hwker
  have hwzero : w.toAdd = 0 := Submodule.disjoint_def.mp hD w.toAdd hw hwfixed
  change j w = 1
  have hwone : w = 1 := Multiplicative.toAdd.injective hwzero
  rw [hwone,map_one]


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual kernel-intersection commutator avoids the entire opposite
component centralizer. This retains every fixed attachment of the original cover. -/
theorem replacement_kernel_intersection_commutator_disjoint
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Disjoint ⁅Z d.radical z ⊓ Q d.radical a,Q d.radical a⁆
      (centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) := by
  obtain ⟨cv⟩ := replacement_kernel_point_cover h d path hb hat hzt hlarge
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
  exact intersection_commutator_disjoint_of_cover path (by omega) hat hzt _ cv
    (replacement_nonfrattini_Z_eq_moving_sup_edge h d rev hb hzt hl)

/-- The two literal seed commutators have trivial intersection. This is the
paired disjointness used in the source Frattini calculation. -/
theorem replacement_paired_seed_commutators_disjoint
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Disjoint ⁅Sp4Four.secondarySeed d.radical a t z,Q d.radical a⁆
      ⁅Sp4Four.secondarySeed d.radical z t a,Q d.radical z⁆ := by
  have hdis := replacement_kernel_intersection_commutator_disjoint h d path hb hat hzt hlarge
  have hm := (replacement_paired_secondary_bounds h d path hb hat hzt hlarge).2.2.2.2
  apply disjoint_iff_inf_le.mpr
  intro x hx
  apply hdis.le_bot
  refine ⟨?_,?_⟩
  · exact commutator_mono (le_inf (Sp4Four.secondarySeed_le d.radical a t z)
      (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)) le_rfl hx.1
  · exact (centralizer_le ((Ltilde_le_stabilizer z).trans le_sup_right)) (hm hx).2

/-- The original secondary orbits have disjoint ambient Frattini subgroups. -/
theorem replacement_paired_frattini_disjoint
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    Disjoint ((frattini A).map A.subtype) ((frattini A').map A'.subtype) := by
  obtain ⟨_,_,hphi,hphi',_⟩ := replacement_paired_secondary_bounds h d path hb hat hzt hlarge
  exact (replacement_paired_seed_commutators_disjoint h d path hb hat hzt hlarge).mono hphi hphi'


/-- The full preimage of the component-fixed secondary quotient centralizes
the actual secondary group, including its Z-layer. -/
theorem replacement_secondary_fixed_preimage_centralizes
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    commutatorPreimage A (Ltilde d.radical a) (Z d.radical a) ≤
      centralizer (A : Set (FreeAmalgam d.radical)) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let L₀ := Ltilde d.radical a
  let Z₀ := Z d.radical a
  let D := commutatorPreimage A L₀ Z₀
  have hAQ : A ≤ Q d.radical a := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hZA : Z₀ ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)).trans
      (centralizer_le hAQ)
  have hAN : A ≤ normalizer Z₀ :=
    (le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _)
  have hDA : D ≤ A := commutatorPreimage_le _ _ _
  have hDLA : ⁅⁅L₀,D⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm]
    exact (commutator_commutatorPreimage_le A L₀ Z₀ hAN).trans hZA
  have hDAL : ⁅⁅D,A⁆,L₀⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (commutator_mono hDA hAQ).trans
      (((replacement_secondary_commutator_eq_seed h d path hb hat hzt hlarge).2.trans
        inf_le_right).trans (centralizer_le (Ltilde_le_stabilizer a)))
  have hALD : ⁅⁅A,L₀⁆,D⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hDLA hDAL
  have he : A = ⁅A,L₀⁆ ⊔ Z₀ := by
    rw [replacement_secondary_component_commutator_eq_core h d path hb hat hzt hlarge]
    exact replacement_secondary_eq_core_sup_Z h d path hb hat hzt hlarge
  apply le_centralizer_iff.mp
  change A ≤ centralizer (D : Set (FreeAmalgam d.radical))
  rw [he]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hALD)
    (hZA.trans (centralizer_le hDA))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
