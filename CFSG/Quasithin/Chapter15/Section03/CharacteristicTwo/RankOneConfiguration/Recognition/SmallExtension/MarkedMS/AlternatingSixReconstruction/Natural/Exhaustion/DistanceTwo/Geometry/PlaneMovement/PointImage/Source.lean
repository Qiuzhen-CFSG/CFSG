module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.CriticalTransposition
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.Nonquadratic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.PointImage.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Selection.BaseEdge

/-!
# The actual replacement image is a point core

At the base edge, the selected opposite orbit fills the radical quotient.
Its faithful quadratic action proves that this quotient is elementary of
order eight. The other elementary-eight class acts quadratically on both
possible whole moved covers, contradicting the source displacement.
Consequently the literal projection maps the radical onto a conjugate point
core; no point marking or natural complement is assumed.

LocalCalculations and radical-derived containment remain explicit earlier
premises. Their construction remains with qt-e-ms-small-a6-exhaustion-distance-two;
this theorem does not discharge LocalImageInput. The literal whole-core
application is in Assembly/PointImage/Source.lean.
Source: MS93 (3.6), printed pp.870--871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
open LargeDistance PairEstimates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
theorem radical_image_elementary_eight
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup) :
    IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)) ∧
      Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 8 := by
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  obtain ⟨o,ho⟩ := exists_orderedOrbit_base (replacementGeometry h d) hp hQR hl hb
  let a := earlyPair hp hQR hl hb hlarge o
  let s := sourceImageModel h e hz hn d a
  let q := Recognition.sourceProjection h e hz hn d
  let := a.quotient_elementary
  have hfull := (images_full a s hp hQR hder).1
  have hbeta : a.b = beta d.radical := ho
  rw [hbeta,Q_alpha d.radical hp hQR,Q_beta] at hfull
  have hnative : a.opposite.comap (embedM d.radical) ⊔ pCore 2 d.overgroup = d.radical := by
    apply map_injective (embedM_injective d.radical)
    rw [Subgroup.map_sup,a.opposite_map]
    exact hfull
  have hmap : (a.opposite.comap (embedM d.radical)).map q = d.radical.map q := by
    have he := congrArg (Subgroup.map q) hnative
    rw [Subgroup.map_sup,←Recognition.sourceProjection_kernel h e hz hn d,map_ker_self,sup_bot_eq] at he
    exact he
  let := s.actor_elementary hp hQR
  have helem : IsElementaryAbelian 2 ((s.actor).map s.projection.range.subtype) :=
    IsElementaryAbelian.map _
  have heq : (s.actor).map s.projection.range.subtype = d.radical.map q := by
    change ((a.opposite.comap (embedM d.radical)).map q.rangeRestrict).map q.range.subtype = _
    rw [map_map,MonoidHom.subtype_comp_rangeRestrict,hmap]
  refine ⟨heq ▸ helem,?_⟩
  rw [←heq,card_map_of_injective s.projection.range.subtype_injective,s.actor_card hp hQR]
  exact (s.strict_indices hp hQR).1

include h e hz hn in
theorem moved_action_nonquadratic
    (hq : Function.Surjective (Recognition.sourceProjection h e hz hn d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    letI := replacementMoved_normal h d
    letI := moved_elementary h d
    let q := Recognition.sourceProjection h e hz hn d
    let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
    ¬ IsQuadratic (NormalElementaryQuotient.representation (replacementMoved d) q hq hk)
      (d.radical.map q) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let q := Recognition.sourceProjection h e hz hn d
  let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
    (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  change ¬ IsQuadratic ρ (d.radical.map q)
  intro hquad
  apply moved_displacement_not_le_seed h e hz d hb hlarge
  have hR : W ≤ d.radical := (replacementMoved_le_omegaCenter h d).trans
    ((omegaCenter_le _).trans (replacement_core_le_radical h d))
  have hWC : ⁅d.radical,W⁆ ≤ W := commutator_le_right _ _
  have hfix : ∀ x ∈ ⁅d.radical,W⁆, ∀ r ∈ d.radical, r*x*r⁻¹=x := by
    intro x hx r hr
    have hxspace : Additive.ofMul (⟨x,hWC hx⟩ : W) ∈
        subspaceCommutator ρ ⊤ (d.radical.map q) := by
      rw [←NormalElementaryQuotient.commutatorSpace_eq W q hq hk]
      change x ∈ ⁅W,d.radical⁆
      rwa [commutator_comm]
    have hfixed : subspaceCommutator ρ ⊤ (d.radical.map q) ≤
        LinearMap.ker (ρ (q r) - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,_,rfl⟩
      change ρ (q r) (ρ b v-v) - (ρ b v-v)=0
      rw [hquad _ (mem_map_of_mem q hr) b hb v,sub_self]
    have he : ρ (q r) (Additive.ofMul (⟨x,hWC hx⟩ : W)) =
        Additive.ofMul (⟨x,hWC hx⟩ : W) := by
      simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]
        using hfixed hxspace
    exact (NormalElementaryQuotient.representation_apply W q hq hk r
      (Additive.ofMul (⟨x,hWC hx⟩ : W))).symm.trans
        (congrArg (fun v : Additive W => v.toMul.val) he)
  intro x hx
  apply mem_omegaCenter_iff.mpr
  refine ⟨hR (hWC hx),elemPow_eq_one_of_isElementaryAbelian (p := 2) x (hWC hx),?_⟩
  intro r hr
  exact mul_inv_eq_iff_eq_mul.mp (hfix x hx r hr)

include h e hz hn in
theorem radical_image_point_core
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup) :
    ∃ g, d.radical.map (Recognition.sourceProjection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨hel,hcard⟩ := radical_image_elementary_eight h e hz hn d hl hb hlarge hder
  let := hel
  rcases elementary_eight_models _ hcard with ⟨g,hg⟩ | he
  · have hq := LocalImages.sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge
    let := replacementMoved_normal h d
    let := moved_elementary h d
    let q := Recognition.sourceProjection h e hz hn d
    let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
    let ρ := NormalElementaryQuotient.representation (replacementMoved d) q hq hk
    have hquad : IsQuadratic (coreRepresentation (Fin 6)) (d.radical.map q) := by
      rw [hg]
      exact quadratic_conjugate _ _ ordinary_core_quadratic g
    exfalso
    apply moved_action_nonquadratic h e hz hn d hq hb hlarge
    rcases moved_cover_model h e hz hn d hq with ⟨E,hE⟩ | ⟨E,hE⟩
    · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
      apply quadratic_of_equivariant_surjection (coreRepresentation (Fin 6)) ρ
        f (E.symm.surjective.comp coreToNatural_surjective) _ _ hquad
      intro g v
      apply E.injective
      rw [hE]
      change E (E.symm (coreToNatural (Fin 6) (coreRepresentation (Fin 6) g v))) =
        naturalRepresentation (Fin 6) g (E (E.symm (coreToNatural (Fin 6) v)))
      rw [E.apply_symm_apply,E.apply_symm_apply,coreToNatural_equivariant]
    · apply quadratic_of_equivariant_surjection (coreRepresentation (Fin 6)) ρ
        E.symm.toLinearMap E.symm.surjective _ _ hquad
      intro g v
      apply E.injective
      change E (E.symm (coreRepresentation (Fin 6) g v)) = E (ρ g (E.symm v))
      rw [E.apply_symm_apply,hE,E.apply_symm_apply]
      rfl
  · exact he

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
