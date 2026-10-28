module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThreeContained
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeMovement

/-!
# The original whole-core movement in MS93 (3.7)(3)

The original Q/C_Q(L) is a natural dual cover. The dual fixed-vector lifting
argument realizes every displacement on this section by a vector in its
embedded natural module, with the same actor. The full coordinate map lifts
this to [Q,A] <= [U,A] C_Q(L). For the actual opposite critical Z-layer,
restoring its full central supplement gives [Q,Z'] <= [Z,Z'] C_Q(L).

The companion SourceThreeNoncontained uses this bound in the actual
component-radical intersection and generator contradiction. SourceThree
applies the resulting theorem to the selected original star, with shortness
and innerness discharged and the original marking and all fixed attachments
retained. The remaining paired fixed-kernel equality, critical-pair selection,
original Sylow branch, minimum marked preservation and saturation, field
restriction and block assembly are separate source obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(3), printed p.874, using the dual of (1.5)(ii).
The internal import reuses only the generic dual-module lifting proof;
its saturated-replacement action is not transferred to the original graph.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Each original whole-core displacement lifts from its natural layer
modulo the complete fixed factor, with the same actor. -/
theorem original_whole_core_displacement_le
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {a : Vertex R} (ha : color R a=false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a) :
    ⁅Q R a,A⁆ ≤ ⁅U R a,A⁆ ⊔ fixedCore R a := by
  obtain ⟨E,hE,s,γ,_hγinj,hγ,_hmap,i,hi,hd,hrange,_⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort ha
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun B : Subgroup H => B.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  let π := s.sectionData.coordinates
  let cm (x : stabilizer R a) (y : Q R a) : Q R a :=
    (⟨x.val*y.val*x.val⁻¹,
      (mem_normalizer_iff.mp (s.sectionData.normalized x.property) y).mp y.property⟩ : Q R a)*y⁻¹
  have hcm (x : stabilizer R a) (y : Q R a) :
      (π (cm x y)).toAdd=s.action (s.quotient x) (π y).toAdd-(π y).toAdd := by
    dsimp only [cm,π]
    rw [map_mul,map_inv]
    change (s.sectionData.coordinates ⟨x.val*y.val*x.val⁻¹,_⟩).toAdd +
      -(s.sectionData.coordinates y).toAdd = _
    rw [s.sectionData.equivariant,sub_eq_add_neg]
    rfl
  rw [commutator_comm (Q R a)]
  apply commutator_le.mpr
  intro x hx y hy
  let xs : stabilizer R a := ⟨x,hA hx⟩
  let yq : Q R a := ⟨y,hy⟩
  obtain ⟨b,hbq⟩ := hγonto (s.quotient xs)
  obtain ⟨v,hv⟩ := dual_displacement_lifts i hi hd b (π yq).toAdd
  obtain ⟨u,hu,heu⟩ := (hrange (i v)).mp ⟨v,rfl⟩
  have he : π (cm xs yq)=π (cm xs u) := by
    apply Multiplicative.toAdd.injective
    rw [hcm,hcm,heu,←hbq]
    change (s.action.comp γ) b (π yq).toAdd-(π yq).toAdd =
      (s.action.comp γ) b (i v)-i v
    rw [hv,←i.isIntertwining,map_sub]
  have hk : ((cm xs u)⁻¹*cm xs yq).val ∈ fixedCore R a := by
    apply (s.sectionData.coordinates_eq_one_iff _).mp
    change π ((cm xs u)⁻¹*cm xs yq)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hc : (cm xs u).val ∈ ⁅U R a,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hx hu
  have hh := (⁅U R a,A⁆ ⊔ fixedCore R a).mul_mem
    (mem_sup_left hc) (mem_sup_right hk)
  change (cm xs u).val*((cm xs u).val⁻¹*(cm xs yq).val) ∈ _ at hh
  have hh' : (cm xs yq).val ∈ ⁅U R a,A⁆ ⊔ fixedCore R a := by
    simpa only [mul_inv_cancel_left] using hh
  exact hh'

/-- The whole-core movement used in source (3.7)(3), retaining the full
fixed attachment and the literal opposite critical layer. -/
theorem original_source_three_whole_core_movement
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Q R a,Z R z⁆ ≤
      ⁅Z R a,Z R z⁆ ⊔ fixedCore R a := by
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hh := original_whole_core_displacement_le h hshort hinner path.start_color (Z R z) hZA
  rwa [←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt] at hh



end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
