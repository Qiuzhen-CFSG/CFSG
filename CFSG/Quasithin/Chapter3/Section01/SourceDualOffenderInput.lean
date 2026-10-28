module
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.SmallSupport
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.CubicRatio
/-!
# The original qrc action on its dual offender subgroup

The simple QTKE and maximal two-local hypotheses supply an actual SQTK
cover of the faithful image on V. Restriction to the normal subgroup generated
by dual best offenders inherits faithfulness and the trivial two-core. This
constructs precisely the source B.5 input on the literal original module.

Restriction can only increase the quadratic ratio. If the Fitting subgroup
of this restricted actor moves the dual module, the proved B.1 plane argument
therefore bounds the original cubic ratio by two.

Source: Aschbacher--Smith B.5.13 and 3.1.6--8, printed pp.110--112,573--576.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The faithful action image is a quotient of the actual local SQTK subgroup. -/
theorem QrcHypotheses.image_sqtkQuotient
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M) :
    Nonempty (SQTKQuotient K (internalActionImage M₀ V h.module_normalized)) := by
  have hS := hG.twoLocal_sqtk hM.1
  have hs : IsSQTK K M₀ :=
    ⟨hS.stronglyQuasithin.of_injective (inclusion h.left_le) (inclusion_injective h.left_le),
      hS.isKGroup.of_injective (inclusion h.left_le) (inclusion_injective h.left_le)⟩
  exact ⟨{
    Cover := M₀
    kernel := (actionHom M₀ V h.module_normalized).ker
    sqtk := hs
    equiv := actionQuotientEquiv M₀ V h.module_normalized }⟩

/-- Every source B.5 hypothesis holds on the original dual offender subgroup. -/
theorem QrcHypotheses.dual_offender_source
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M) :
    letI := h.module_elementary
    let ρ := imageRepresentation M₀ V h.module_normalized
    FFHypothesis K
      (Representation.dual (ρ.comp (offenderSubgroup ρ.dual).subtype)) := by
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  obtain ⟨c⟩ := h.image_sqtkQuotient hG hM
  let N := offenderSubgroup ρ.dual
  let : N.Normal := offenderSubgroup_normal ρ.dual
  have hncore : pCore 2 N = ⊥ := by
    have hle : (pCore 2 N).map N.subtype ≤ pCore 2 (internalActionImage M₀ V h.module_normalized) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
    rw [h.module_reduced] at hle
    exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp (bot_unique hle)
  exact {
    finite_module := inferInstance
    faithful := (faithful_dual ρ (imageRepresentation_injective M₀ V h.module_normalized)).comp
      N.subtype_injective
    twoCore := hncore
    generated := offenderSubgroup_restrict_eq_top ρ.dual
    quotient := ⟨c.subgroup N⟩ }

omit [Finite G] in
/-- Restricting the original actor preserves every available quadratic witness. -/
theorem QrcHypotheses.quadraticRatio_le_dual_offender_restriction
    (h : QrcHypotheses T M M₀ H V) :
    letI := h.module_elementary
    let ρ := imageRepresentation M₀ V h.module_normalized
    quadraticRatio ρ ≤ quadraticRatio (ρ.comp (offenderSubgroup ρ.dual).subtype) := by
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  let N := offenderSubgroup ρ.dual
  exact quadraticRatio_le_of_injective_equivariant (ρ.comp N.subtype) ρ
    N.subtype N.subtype_injective (LinearEquiv.refl _ _) (fun _ _ => rfl)

/-- The nonzero Fitting-moved branch already gives the original numerical conclusion. -/
theorem QrcHypotheses.cubicRatio_le_two_of_dual_fittingMoved
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hm : letI := h.module_elementary
      let ρ := imageRepresentation M₀ V h.module_normalized
      ChapterB.FittingStructure.fittingMoved (Representation.dual (ρ.comp (offenderSubgroup ρ.dual).subtype)) ≠ ⊥) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let := h.module_elementary
  let ρ := imageRepresentation M₀ V h.module_normalized
  let σ : Representation (ZMod 2) (offenderSubgroup ρ.dual) (Additive V) :=
    ρ.comp (offenderSubgroup ρ.dual).subtype
  have hs := h.dual_offender_source hG hM
  exact (cubicRatio_le_quadraticRatio ρ).trans
    (h.quadraticRatio_le_dual_offender_restriction.trans
      (ChapterB.SourceB513.quadraticRatio_le_two_of_dual_fittingMoved σ hs.faithful hs.twoCore hm))
end CFSG.Quasithin.Chapter3
