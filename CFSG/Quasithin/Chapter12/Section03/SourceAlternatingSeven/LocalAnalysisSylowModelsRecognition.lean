module

public import Theory.Representation.BinarySevenCode.WeightSixResidual
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceFive
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotientsSource
public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion

/-!
# The literal point quotients in the contrary A₇ normalizer branch

The weight-six point centralizer is the preimage of its actual A₆ word
stabilizer. Its perfect residual still maps onto that stabilizer. In the
contrary-normalizer branch the earlier block theorem gives L/O₂(L) ≅ A₇,
so the original projection has two-group kernel. Restricting that same
projection identifies the residual's two-core quotient, and hence its
O₂,Z quotient, with A₆.

The weight-two quotient is the already proved literal A₅ quotient from
`LocalAnalysisCentralizersThompsonSourceFive`. The final paired theorem
supplies both quotient inputs of `Points.models_of_quotients`; the common
core is proved in the companion module. The Sylow-normalizer assembly
owns the discharge of the contrary hypothesis.

Source: Aschbacher--Smith, 3.3.22, printed pp.597--598, used in 12.3.5.
-/

public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

private lemma center_eq_bot_of_alternating_equiv {A : Type*} [Group A]
    {n : ℕ} (hn : 4 ≤ n) (e : A ≃* alternatingGroup (Fin n)) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center (alternatingGroup (Fin n)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨a,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [alternatingGroup.center_eq_bot (by simpa using hn),mem_bot] at he
  exact e.map_eq_one_iff.mp he

namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

/-- The perfect residual covers the entire marked A₆ stabilizer. -/
lemma six_residual_image (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    ((SylowNormalizer.pointResidual L (v : G)).subgroupOf L).map S.projection =
      WeightTwoGeometry.stabilizer (E.coordinates v).toAdd := by
  let C := L ⊓ centralizer ({(v : G)} : Set G)
  have hCL : C ≤ L := inf_le_left
  let e : C ≃* C.subgroupOf L := (subgroupOfEquivOfLe hCL).symm
  have hm := map_solvableResidual_eq e.toMonoidHom e.surjective
  have htrans : ((SylowNormalizer.pointResidual L (v : G)).subgroupOf L) =
      (solvableResidual (C.subgroupOf L)).map (C.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left),
      ← hm, map_map, map_map]
    rfl
  let := WeightSixGeometry.stabilizer_perfect (E.coordinates v).toAdd hv
  rw [htrans, E.point_centralizer_subgroupOf_eq_comap,
    map_solvableResidual_comap S.projection S.projection_surjective,
    solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

/-- Restrict the original projection to its actual weight-six image. -/
@[expose] def sixResidualProjection (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    SylowNormalizer.pointResidual L (v : G) →*
      WeightTwoGeometry.stabilizer (E.coordinates v).toAdd :=
  (S.projection.comp (inclusion ((SylowNormalizer.pointResidual_le L (v : G)).trans
    inf_le_left))).codRestrict _ (fun x =>
      (E.six_residual_image v hv).le (mem_map_of_mem S.projection x.property))

lemma sixResidualProjection_surjective (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    Function.Surjective (E.sixResidualProjection v hv) := by
  intro a
  obtain ⟨l,hl,he⟩ := (E.six_residual_image v hv).ge a.property
  exact ⟨⟨l,hl⟩,Subtype.ext he⟩

/-- The simple two-core quotient removes precisely the central-cover part
of the original projection kernel. -/
lemma projection_kernel_isTwoGroup_of_seven
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    IsPGroup 2 S.projection.ker := by
  have he : S.projection.ker = pCore 2 L := by
    rw [Setup.projection, MonoidHom.ker_comp_of_injective _ _ S.quotient.injective,
      QuotientGroup.ker_mk']
    exact centralPreimage_eq_of_center_quotient_eq_bot _
      (center_eq_bot_of_alternating_equiv (by decide) eL)
  rw [he]
  exact pCore_isPGroup

lemma sixResidualProjection_kernel_isTwoGroup (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    IsPGroup 2 (E.sixResidualProjection v hv).ker := by
  rw [sixResidualProjection, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
  exact (projection_kernel_isTwoGroup_of_seven (S := S) eL).comap_of_injective _
    (inclusion_injective _)

/-- The actual residual quotient, induced by the restricted source projection. -/
noncomputable def sixResidualCoreEquiv (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    (SylowNormalizer.pointResidual L (v : G) ⧸
      pCore 2 (SylowNormalizer.pointResidual L (v : G))) ≃* alternatingGroup (Fin 6) := by
  let e := WeightSixGeometry.sixEquiv (E.coordinates v).toAdd hv
  let f := e.toMonoidHom.comp (E.sixResidualProjection v hv)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact E.sixResidualProjection_kernel_isTwoGroup v hv eL
  exact (f.pCoreQuotientEquiv (e.surjective.comp (E.sixResidualProjection_surjective v hv)) hk).trans
    ((QuotientGroup.quotientMulEquivOfEq
      alternatingGroup.SevenComponent.alternating_six_twoCore).trans QuotientGroup.quotientBot)

end Setup.NaturalCoordinates
namespace SylowNormalizer.Points
variable {E : S.NaturalCoordinates} (P : Points E)

/-- The literal O₂,Z quotient of the original weight-six residual. -/
noncomputable def sixCentralEquivOfSeven
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6) := by
  let e := E.sixResidualCoreEquiv P.six P.six_weight eL
  have hz : center (P.sixGroup ⧸ pCore 2 P.sixGroup) = ⊥ := by
    exact center_eq_bot_of_alternating_equiv (by decide) e
  exact (QuotientGroup.quotientMulEquivOfEq
    (centralPreimage_eq_of_center_quotient_eq_bot _ hz)).trans e

/-- Both local recognition inputs with no assumed model isomorphism. -/
lemma point_quotients_of_contrary_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty ((P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient structural hescape
  exact ⟨⟨P.fiveCoreEquiv⟩, ⟨P.sixCentralEquivOfSeven eL⟩⟩
end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
