module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaRecognition
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalOvergroupModels

/-!
# The four field-four overgroup models from marked Omega recognition

The Omega numerical and chief-section arguments discharge the larger-Omega
commutator input in the original overgroup classifier. The original component
supplies its cubic action; nonzero overgroup two-core supplies the stabilizer
Sylow marking. The result retains the literal fully moved action and gives
the four linear, repeated-linear, symplectic and G₂ models over the field
of order four, without separately choosing a cubic actor or Sylow witness.

The earlier E.2.7 marked recognition, old A₅ quotient, nonzero core, and
line-centralization and plane-movement source inputs remain explicit.
Source: Aschbacher--Smith 9.2.2 and 9.3.6--7, printed pp.730,733--734.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
  {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
  (hrec : (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel →
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q))
include m hH hrec

/-- Original field-four action models with the Omega commutator, chosen cubic,
and stabilizer Sylow premises discharged by their proved source arguments. -/
theorem old_residual_overgroup_fourField_models_of_symplectic_recognition
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
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
  m.old_residual_overgroup_fourField_models_of_nonzero_core
    m.sylow_not_normalizes_component houtside
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)
    hH eK M₀ hcore hgen hKU hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
