module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsCore
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowModelsRecognition

/-!
# LocalAnalysisSylowModelsCore at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowModelsCore`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

lemma six_join_normalizes_module_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    P.sixGroup ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le (((pointResidual_le L (P.six : G)).trans inf_le_left).trans S.chosen.normalizes)
    (((structural L S.hypothesis).2.2 V S.chosen).1)

def sixJoinPermutation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (P.sixGroup ⊔ (T : Subgroup G) : Subgroup G) →*
      WeightTwoGeometry.symmetricStabilizer (E.coordinates P.six).toAdd :=
  ((E.sourceNormalizerModel_at structural).permutation.comp
    (inclusion (P.six_join_normalizes_module_at structural))).codRestrict _ (fun h => by
      rw [WeightTwoGeometry.mem_symmetricStabilizer]
      have hc : P.sixGroup ⊔ (T : Subgroup G) ≤ centralizer ({(P.six : G)} : Set G) :=
        sup_le ((pointResidual_le L (P.six : G)).trans inf_le_right)
          (fun t ht => mem_centralizer_singleton_iff.mpr (P.six_central t ht))
      change evenRepresentation ((E.sourceNormalizerModel_at structural).permutation
        (inclusion (P.six_join_normalizes_module_at structural) h))
        ((E.sourceNormalizerModel_at structural).coordinates P.six).toAdd =
        ((E.sourceNormalizerModel_at structural).coordinates P.six).toAdd
      rw [← (E.sourceNormalizerModel_at structural).equivariant]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hc h.property)))

lemma sixJoinPermutation_contains_stabilizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (a : WeightTwoGeometry.stabilizer (E.coordinates P.six).toAdd) :
    ∃ h : (P.sixGroup ⊔ (T : Subgroup G) : Subgroup G),
      (P.sixJoinPermutation_at structural h).val = a.val.val := by
  obtain ⟨k,hk⟩ := E.sixResidualProjection_surjective P.six P.six_weight a
  refine ⟨⟨k,mem_sup_left k.property⟩,?_⟩
  have he := E.sourceNormalizerModel_component_at structural
    ⟨k,((pointResidual_le L (P.six : G)).trans inf_le_left) k.property⟩
  exact he.trans (congrArg
    (fun b : WeightTwoGeometry.stabilizer (E.coordinates P.six).toAdd => b.val.val) hk)

lemma six_core_le_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
  have hT : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (P.sixGroup ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  refine le_inf hT ?_
  rintro _ ⟨q,hq,rfl⟩ v hv
  let v' : V := ⟨v,hv⟩
  have hf := WeightSixGeometry.twoCore_maps_trivially (E.coordinates P.six).toAdd
    P.six_weight (P.sixJoinPermutation_at structural)
    (P.sixJoinPermutation_contains_stabilizer_at structural) ⟨q,hq⟩
  have hp : (E.sourceNormalizerModel_at structural).permutation
      (inclusion (P.six_join_normalizes_module_at structural) q) = 1 :=
    congrArg Subtype.val hf
  have he := (E.sourceNormalizerModel_at structural).equivariant
    (inclusion (P.six_join_normalizes_module_at structural) q) v'
  rw [hp, map_one] at he
  have hh : V.normalizerMonoidHom
      (inclusion (P.six_join_normalizes_module_at structural) q) v' = v' :=
    E.coordinates.injective (Multiplicative.toAdd.injective he)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm

lemma six_core_eq_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  le_antisymm (P.six_core_le_core_at structural) P.core_le_six_core

noncomputable def modelsOfSeven_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) : P.Models :=
  P.models_of_quotients P.fiveCoreEquiv (P.sixCentralEquivOfSeven eL)
    (P.six_core_eq_core_at structural)

lemma models_of_contrary_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) : Nonempty P.Models := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient_at structural hescape
  exact ⟨P.modelsOfSeven_at structural eL⟩

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

