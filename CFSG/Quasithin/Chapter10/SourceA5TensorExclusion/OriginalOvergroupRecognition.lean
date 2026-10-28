module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalOvergroupModels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaRecognition
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPlaneMovement

/-!
# Original field-four action models from the remaining source recognition

For the original tensor setup and its actual H-star member, the marked E.2.7
pair supplies the Omega numerical bound. The chief-section argument gives the
needed commutator containment; H-star itself supplies the outside-maximal
guard, and the intrinsic cubic gives the core and center conclusions.
An actual cubic subgroup in the old residual and local orbit supplies plane
movement. The resulting B.5 action has one of the four field-four markings.

The old A₅ quotient, original line centralization, nontrivial new two-core,
and actual old cubic subgroup remain separate earlier source inputs. The
concrete carrier corollary is about the literal action image, retaining the
centralizer kernel rather than identifying it with a two-core quotient.

Source: Aschbacher–Smith 9.2.2 and 9.3.4–7, printed pp.730–734.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_overgroup_models_of_symplectic_recognition
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hrec : (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel →
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q))
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3) :
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
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  have hHcore : pCore 2 H ≠ ⊥ := by
    intro hb
    apply hH.1.1.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [hb,Subgroup.map_bot]
  obtain ⟨M,hM,hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hHcore
  have houtside : Chapter3.HasMaximalOutside T D.maximalLocal :=
    Chapter3.hasMaximalOutside_of_two_distinct
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hM
      (le_normalizer_componentOrbit L T) (hH.1.1.2.trans hHM)
      (fun he => hH.1.2 (he ▸ hHM))
  exact m.old_residual_overgroup_fourField_models_of_nonzero_core
    m.sylow_not_normalizes_component houtside
    (m.omegaCenter_core_commutator_le_of_symplectic_recognition hH hrec)
    hH eK M₀ hcore hgen hKU
    (m.old_residual_moves_tensorPlane_of_cartan H B hBK hBL hB)

theorem old_residual_overgroup_action_image_models
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hrec : (m.omegaCenter_core_qrcHypotheses hH).HasSymplecticMiddleOutsideCoreModel →
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      let S := T.subtype hH.1.1.2
      let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)
      ChapterE.Witnesses.SymplecticFour.HasRecognizedPair
        (S.mapSurjective (QuotientGroup.mk'_surjective _))
        ((ChapterB.minimalParabolicMax S hp).map q)
        (((omegaCenterIn ((localJoin T L).pCoreIn 2)).subgroupOf H).map q))
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBL : B ≤ localOrbit T L) (hB : Nat.card B = 3) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal
      Nonempty (((pResidual 2 M₀).map (actionMk W)) ≃*
        SL(3,ChapterB.QuasisimpleSource.BinaryField.four.Carrier)) ∨
      Nonempty (((pResidual 2 M₀).map (actionMk W)) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) ∨
      Nonempty (((pResidual 2 M₀).map (actionMk W)) ≃*
        Atlas.G2.Model ChapterB.QuasisimpleSource.BinaryField.four.Carrier) := by
  obtain ⟨hU,hHe,hF,hZ,hr,hUW,hKN,hm,h,hs⟩ :=
    m.old_residual_overgroup_models_of_symplectic_recognition hH hrec eK M₀ hcore hgen hKU B hBK hBL hB
  let := hr.normal
  let := hr.elementary
  refine ⟨hU,hHe,hF,hZ,hr,?_⟩
  let i := (subgroupOfEquivOfLe hKN).symm
  rcases hs.actor_models with ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨i.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨i.trans a⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨i.trans a⟩)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
