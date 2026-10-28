module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsRecognition

/-!
# The common two-core and the actual A₇ point models

The original weight-six residual and T fix the same six-letter word.
Their permutation image contains its full A₆ stabilizer, so the lower
weight-six calculation kills the image of their normal two-core. That
core therefore lies in C_T(V) = O₂(LT). Sylow containment gives the reverse
inclusion. This proves the source common-core identity without a quotient
identification or an ambient fusion hypothesis.

The final constructors combine this equality with the literal point
quotients and the existing A₅ image transport to construct `Points.Models`.
The contrary-normalizer assumption is discharged in
`LocalAnalysisSylowNormalizer`; no source callback remains here.

Source: Aschbacher--Smith, 3.3.22, printed pp.597--598, used in 12.3.5.
-/

@[expose] public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace SylowNormalizer.Points
variable {E : S.NaturalCoordinates} (P : Points E)

lemma six_join_normalizes_module
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    P.sixGroup ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le (((pointResidual_le L (P.six : G)).trans inf_le_left).trans S.chosen.normalizes)
    (((structural G T L S.hypothesis).2.2 V S.chosen).1)

/-- The literal permutation action of the weight-six residual Sylow join. -/
def sixJoinPermutation
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (P.sixGroup ⊔ (T : Subgroup G) : Subgroup G) →*
      WeightTwoGeometry.symmetricStabilizer (E.coordinates P.six).toAdd :=
  ((E.sourceNormalizerModel structural).permutation.comp
    (inclusion (P.six_join_normalizes_module structural))).codRestrict _ (fun h => by
      rw [WeightTwoGeometry.mem_symmetricStabilizer]
      have hc : P.sixGroup ⊔ (T : Subgroup G) ≤ centralizer ({(P.six : G)} : Set G) :=
        sup_le ((pointResidual_le L (P.six : G)).trans inf_le_right)
          (fun t ht => mem_centralizer_singleton_iff.mpr (P.six_central t ht))
      change evenRepresentation ((E.sourceNormalizerModel structural).permutation
        (inclusion (P.six_join_normalizes_module structural) h))
        ((E.sourceNormalizerModel structural).coordinates P.six).toAdd =
        ((E.sourceNormalizerModel structural).coordinates P.six).toAdd
      rw [← (E.sourceNormalizerModel structural).equivariant]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hc h.property)))

lemma sixJoinPermutation_contains_stabilizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (a : WeightTwoGeometry.stabilizer (E.coordinates P.six).toAdd) :
    ∃ h : (P.sixGroup ⊔ (T : Subgroup G) : Subgroup G),
      (P.sixJoinPermutation structural h).val = a.val.val := by
  obtain ⟨k,hk⟩ := E.sixResidualProjection_surjective P.six P.six_weight a
  refine ⟨⟨k,mem_sup_left k.property⟩,?_⟩
  have he := E.sourceNormalizerModel_component structural
    ⟨k,((pointResidual_le L (P.six : G)).trans inf_le_left) k.property⟩
  exact he.trans (congrArg
    (fun b : WeightTwoGeometry.stabilizer (E.coordinates P.six).toAdd => b.val.val) hk)

/-- The weight-six join core centralizes the chosen natural module. -/
lemma six_core_le_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
  have hT : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (P.sixGroup ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  refine le_inf hT ?_
  rintro _ ⟨q,hq,rfl⟩ v hv
  let v' : V := ⟨v,hv⟩
  have hf := WeightSixGeometry.twoCore_maps_trivially (E.coordinates P.six).toAdd
    P.six_weight (P.sixJoinPermutation structural)
    (P.sixJoinPermutation_contains_stabilizer structural) ⟨q,hq⟩
  have hp : (E.sourceNormalizerModel structural).permutation
      (inclusion (P.six_join_normalizes_module structural) q) = 1 :=
    congrArg Subtype.val hf
  have he := (E.sourceNormalizerModel structural).equivariant
    (inclusion (P.six_join_normalizes_module structural) q) v'
  rw [hp, map_one] at he
  have hh : V.normalizerMonoidHom
      (inclusion (P.six_join_normalizes_module structural) q) v' = v' :=
    E.coordinates.injective (Multiplicative.toAdd.injective he)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm

/-- Source 3.3.22: the two Sylow joins have the same embedded two-core. -/
lemma six_core_eq_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  le_antisymm (P.six_core_le_core structural) P.core_le_six_core

/-- Construct every local-model field from the actual A₇ two-core quotient. -/
noncomputable def modelsOfSeven
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) : P.Models :=
  P.models_of_quotients P.fiveCoreEquiv (P.sixCentralEquivOfSeven eL)
    (P.six_core_eq_core structural)

/-- The contrary-normalizer source branch supplies the actual local models. -/
lemma models_of_contrary_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) : Nonempty P.Models := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient structural hescape
  exact ⟨P.modelsOfSeven structural eL⟩
end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
