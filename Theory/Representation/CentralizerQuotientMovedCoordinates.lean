module
public import Theory.Representation.CentralizerQuotientAction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.NormalClosureDisplacement
/-!
# The literal commutator subgroup behind a quotient displacement orbit

The centralizer quotient action agrees with the action descended along its
quotient map. The orbit of one displacement is therefore the additive space
of the commutator with that actor's normal closure. If an ambient generation
identity identifies this commutator with [W,H], the same submodule consists
exactly of the original elements of [W,H], through their actual inclusions
in H and W. No abstract module isomorphism replaces those inclusions.

Source application: Aschbacher–Smith 10.2.1 and G.6.2(1), pp.743 and345.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation
open BinaryOffender NormalElementaryQuotient
variable {G : Type*} [Group G] (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]

theorem centralizerQuotient_eq_descended :
    centralizerQuotient U = representation U
      (QuotientGroup.mk' (centralizer (U : Set G))) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) := by
  apply MonoidHom.ext
  intro a
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set G)) a
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (centralizerQuotient_apply U g v).trans
    (representation_apply U _ _ _ g v).symm

theorem centralizerQuotient_conjugateDisplacementSpan (g : G) :
    conjugateDisplacementSpan (centralizerQuotient U)
      (QuotientGroup.mk' (centralizer (U : Set G)) g) ⊤ =
      commutatorSpace U (normalClosure ({g} : Set G)) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  rw [centralizerQuotient_eq_descended,commutatorSpace_eq U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _),
    map_normalClosure _ q (QuotientGroup.mk'_surjective _),Set.image_singleton,
    ←conjugateSpanBy_zpowers_top,commutator_conjugateSpanBy_zpowers]

variable {H W : Subgroup G}
theorem centralizerQuotient_conjugateDisplacementSpan_ambient
    (hW : W ≤ H) [(W.subgroupOf H).Normal] [IsElementaryAbelian 2 (W.subgroupOf H)]
    (g : H) (hgen : ⁅W,H⁆=⁅W,(normalClosure ({g} : Set H)).map H.subtype⁆) :
    conjugateDisplacementSpan (centralizerQuotient (W.subgroupOf H))
      (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)) g) ⊤ =
      AddSubgroup.toZModSubmodule 2
        (((⁅W,H⁆ : Subgroup G).subgroupOf H).subgroupOf (W.subgroupOf H)).toAddSubgroup := by
  rw [centralizerQuotient_conjugateDisplacementSpan]
  have he : ⁅W.subgroupOf H,normalClosure ({g} : Set H)⁆ = (⁅W,H⁆ : Subgroup G).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hW,←hgen,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup W H).trans (sup_le hW le_rfl))]
  unfold commutatorSpace
  rw [he]
theorem centralizerQuotient_conjugateDisplacementSpan_ambient_image
    (hW : W ≤ H) [(W.subgroupOf H).Normal] [IsElementaryAbelian 2 (W.subgroupOf H)]
    (g : H) (hgen : ⁅W,H⁆=⁅W,(normalClosure ({g} : Set H)).map H.subtype⁆) :
    (conjugateDisplacementSpan (centralizerQuotient (W.subgroupOf H))
      (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)) g) ⊤).toAddSubgroup.toSubgroup'.map
      (H.subtype.comp (W.subgroupOf H).subtype) = ⁅W,H⁆ := by
  rw [centralizerQuotient_conjugateDisplacementSpan_ambient hW g hgen]
  have hcW : ⁅W,H⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((normal_subgroupOf_iff_le_normalizer hW).mp inferInstance)
  change ((((⁅W,H⁆ : Subgroup G).subgroupOf H).subgroupOf (W.subgroupOf H))).map
    (H.subtype.comp (W.subgroupOf H).subtype) = _
  rw [←map_map,map_subgroupOf_eq_of_le (subgroupOf_mono H hcW),
    map_subgroupOf_eq_of_le (hcW.trans hW)]

end Representation
