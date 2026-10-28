module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartan
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaComplete

/-!
# The constructed Hall Cartan in the original overgroup models

The actual order-three Hall subgroup inside O²(H) cannot fix the tensor
plane. This removes the independent plane-movement premise from the literal
field-four overgroup classification. The independent source 4.4.3 control,
old-residual A₅ recognition, nonzero overgroup core and line-centralization
premises remain explicit.
Source: Aschbacher--Smith 9.2.7 and 9.3.6--7, printed pp.731--734.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The source Hall Cartan discharges the original old-residual plane movement. -/
theorem old_residual_overgroup_fourField_models_of_control
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ Chapter4.sectionCentralizer (localOrbit T L) →
      B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData :=
  m.old_residual_overgroup_fourField_models_source hH houtside eK M₀ hcore hgen hKU
    (m.old_residual_moves_tensorPlane_of_control hcontrol hH hlarge)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
