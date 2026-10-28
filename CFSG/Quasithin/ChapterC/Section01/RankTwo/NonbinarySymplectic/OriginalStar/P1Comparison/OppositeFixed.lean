module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.OppositeFixedGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivialOpposite
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore

/-!
# The full opposite fixed core misses the original moving layer

In a field-sized critical pair the full midpoint radical moves the opposite
center into the first moving layer. Its cubic elementary natural image has
its fixed vectors inside its displacement, both in the point and plane
cases. The original moving attachment is zero, so this containment lifts
without loss. The opposite fixed/moving intersection therefore belongs to
the first moving attachment and is trivial.

Source: MS93 (3.7), printed p.877, the assertion D_a ∩ U_z = 1. The full
original fixed core is retained; no disjointness or P1-action premise is added.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition ChapterB.QuasisimpleSource

private theorem embedded_fixed_le_commutator
    {E W G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : Function.Bijective p)
    (U T : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : T →* L (K := E))
    (hact : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (β t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hfixed : TwoLocalCover.fixedSpace ((commutator (Sp E)).subtype.comp β).range ≤
      displacementSpace ((commutator (Sp E)).subtype.comp β).range) :
    U ⊓ centralizer (T : Set G) ≤ ⁅U,T⁆ := by
  rintro x ⟨hx,hxc⟩
  obtain ⟨w,rfl⟩ := hjr.symm ▸ hx
  have hfix : p w.toAdd ∈ TwoLocalCover.fixedSpace
      ((commutator (Sp E)).subtype.comp β).range := by
    rintro _ ⟨t,rfl⟩
    have hw : σ (β t) w.toAdd=w.toAdd := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact]
      change t.val*j w*t.val⁻¹=j w
      exact (mul_inv_eq_iff_eq_mul).mpr (hxc t.val t.property)
    change binaryNatural (β t) (p w.toAdd)=p w.toAdd
    rw [←p.isIntertwining,hw]
  obtain ⟨v,hv,hm⟩ := natural_displacement_lifts U T j hjr β σ hact p hp.2
    (p w.toAdd) (hfixed hfix)
  have hvw : v=w.toAdd := hp.1 hv
  rw [hvw,ofAdd_toAdd,commutator_comm] at hm
  exact hm

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

/-- At the actual field-critical pair, the full opposite midpoint movement
belongs to the first moving layer. -/
theorem original_field_critical_edge_displacement_le_moving
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    ⁅Z R z,Q R t⁆ ≤ U R a := by
  have hZS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hUS : U R a ≤ stabilizer R a := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hDS : fixedCore R a ≤ stabilizer R a := inf_le_left.trans (fun _ hx => hx.1)
  have hQa : ⁅Q R a,Z R z⁆ ≤ U R a := by
    rw [(original_source_three_of_field_critical h hshort hinner hnsyl
      g hb path hat hzt hcritical).2.1]
    apply commutator_sup_le_of_relative_normal (stabilizer R a)
      (U R a) (fixedCore R a) (Z R z) (U R a) (U_normalized a) hUS hDS
    · exact le_normalizer_iff_commutator_le_left.mp (hZS.trans (U_normalized a))
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (original_source_fixedCore_centralizes_opposite h hshort hinner hnsyl
          g hb path hat hzt hcritical)).le.trans bot_le
  rw [commutator_comm,←original_component_radical_sup_core h hinner path.start_color hat]
  apply commutator_sup_le_of_relative_normal (stabilizer R a)
    (Q R t ⊓ Ltilde R a) (Q R a) (Z R z) (U R a) (U_normalized a)
    (inf_le_right.trans (Ltilde_le_stabilizer a)) (fun _ hx => hx.1) _ hQa
  rw [commutator_comm]
  exact (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).1

/-- The fixed vectors of the full original cubic radical lie in its actual
moving subgroup. The zero moving attachment makes the natural lifting exact. -/
theorem original_nonsylow_fixed_moving_le_displacement
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false) (hzt : Adjacent R z t) :
    U R z ⊓ centralizer (Q R t : Set (FreeAmalgam R)) ≤ ⁅U R z,Q R t⁆ := by
  obtain ⟨cv⟩ := exists_ambient_cover h hz
  let s := originalMovedSection h
  have hTS : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let β : Q R t →* L (K := cv.field.Carrier) := cv.equiv.groupEquiv.toMonoidHom.comp
    ((cv.quotient.comp (inclusion hTS)).codRestrict
      (K.map (QuotientGroup.mk' (pCore 2 H)))
      (fun _ => (original_component_eq_top hinner).symm.le (mem_top _)))
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp β
  have hα : α=(coverQuotient h hinner cv).comp (inclusion hTS) := by
    apply MonoidHom.ext
    intro x
    exact (coverQuotient_apply h hinner cv (inclusion hTS x)).symm
  have hαk : α.ker=(Q R z).subgroupOf (Q R t) := by
    rw [hα,←MonoidHom.comap_ker,coverQuotient_kernel,comap_inclusion_subgroupOf]
  obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner hz hzt
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hαk.trans hδk.symm)).trans
      (QuotientGroup.quotientKerEquivRange δ))
  let : IsElementaryAbelian 2 δ.range := hδr.symm ▸
    (original_nonsylow_marked_elementary_card h hnsyl).1
  let : IsElementaryAbelian 2 α.range :=
    IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
  have hc : Nat.card α.range=Nat.card cv.field.Carrier^3 := by
    rw [←index_ker,hαk]
    change (Q R z).relIndex (Q R t)=_
    rw [original_nonsylow_full_radical_card h hinner hnsyl hz hzt,
      cv.field.card_eq,cv.degree]
  have hact (x : Q R t) (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd (MovedSection.coverAction s cv.equiv (β x) w))=
        x.val*cv.embedding (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change cv.embedding (Multiplicative.ofAdd (s.space.toRepresentation
      (cv.equiv.groupEquiv.symm (cv.equiv.groupEquiv _)) w))=_
    rw [cv.equiv.groupEquiv.symm_apply_apply]
    exact cv.conjugation (inclusion hTS x) w
  let p := MovedSection.coverProjection s cv.equiv
  have hp : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro w hw
    have hm : cv.embedding (Multiplicative.ofAdd w) ∈
        U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) :=
      ⟨cv.range_eq ▸ ⟨_,rfl⟩,(cv.kernel w).mp hw⟩
    rw [original_source_moving_fixed_attachment_eq_bot h hshort hinner hnsyl g hb hz] at hm
    have hj : cv.embedding (Multiplicative.ofAdd w)=1 := hm
    have he : Multiplicative.ofAdd w=1 := cv.injective (hj.trans (map_one cv.embedding).symm)
    exact congrArg Multiplicative.toAdd he
  apply embedded_fixed_le_commutator (MovedSection.coverAction s cv.equiv) p
    ⟨hp,cv.cover.1⟩ (U R z) (Q R t) cv.embedding cv.injective cv.range_eq β hact
  exact cubic_fixedSpace_le_displacementSpace
    (cv.field.card_eq.trans (congrArg (2^·) cv.degree))
    (by have := h.nonbinary; omega) α.range hc

/-- The opposite moving layer is disjoint from the entire original fixed
core at a field-critical pair, as asserted on printed p.877. -/
theorem original_field_critical_opposite_fixed_disjoint
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    Disjoint (fixedCore R a) (U R z) := by
  have hN := original_source_opposite_fixed_overlap_le_edge h hshort hinner hnsyl
    g hb path hat hzt hcritical
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hcent : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have hmove : fixedCore R a ⊓ U R z ≤ U R a :=
    ((le_inf inf_le_right (hN.trans hcent)).trans
      (original_nonsylow_fixed_moving_le_displacement h hshort hinner hnsyl
        g hb path.end_color hzt)).trans
      ((commutator_mono (U_le_Z z) le_rfl).trans
        (original_field_critical_edge_displacement_le_moving h hshort hinner hnsyl
          g hb path hat hzt hcritical))
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  exact (le_inf hmove inf_le_left).trans
    (disjoint_iff.mp (original_source_moving_disjoint_fixedCore h hshort hinner hnsyl
      g hb path.start_color)).le

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
