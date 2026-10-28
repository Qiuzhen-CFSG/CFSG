module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreDGSResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairFrattini
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Placement

/-!
# Core-profile exclusions for the original tensor configuration

The original 256-element tensor module lies in O₂(L). Under the temporary
O₂(M₀)=1 assumption of 9.3.3, the opposite-factor witness forces S outside L,
so O₂(L S) strictly contains O₂(L). The full original parabolic has this
same enlarged core, and therefore its order is strictly greater than 256.
The Frattini action of that core is reducible: otherwise the core-containment
argument would put S in L. Either an upper bound of 256 or irreducibility
at this literal endpoint consequently proves O₂(M₀) ≠ 1 and supplies the
existing field-four consumer.

For the A5/A5 row, DGS (10.5), p.156, supplies cores of order 16 or 64;
(10.10)(d), p.164, supplies irreducibility in its beta orientation.
Establishing the exhaustive compatible branch and transporting the correct
orientation and full original core remain obligations of
qt-d-tensor-a5-amalgam, using qt-dgs85-source-assembly and its profile and
original-extension producers. The displayed alternative is an explicit
conditional input, not a proved DGS classification or an unconditional
9.3.3 theorem.

Source: DGS85, Groups and Graphs, Part II, (10.5), (10.10), pp.156,164;
Aschbacher--Smith, 9.3.3, p.733, and F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 SourceOldResidualOvergroup
open Chapter4 ChapterB ChapterE ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
open ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The actual tensor endpoint has a core larger than the entire original
256-element tensor module in the hypothetical zero-overgroup-core branch. -/
theorem old_residual_core_zero_parabolic_core_card_gt_256
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    256 < Nat.card (pCore 2 (ChapterF.Source.parabolic
      ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0)) := by
  obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  have hlt := hf.a5_local_core_lt_of_not_contained 0 e (hn 0)
    m.old_residual_common_sylow_not_le_component
  have hcard : Nat.card (ChapterF.Source.twoCore L) <
      Nat.card (ChapterF.Source.twoCore (L ⊔ commonTwo T L)) := by
    apply lt_of_not_ge
    intro hh
    exact hlt.ne (eq_of_le_of_card_ge hlt.le hh)
  have hlower : 256 ≤ Nat.card (ChapterF.Source.twoCore L) := by
    rw [← m.card_fullModule]
    exact card_le_of_le m.fullModule_le_component_core
  have hc := hlower.trans_lt hcard
  have heq := hf.localJoin_twoCore_eq_parabolic hn 0
  change ChapterF.Source.twoCore (L ⊔ commonTwo T L) = _ at heq
  rw [heq] at hc
  simpa only [ChapterF.Source.twoCore, card_subtype] using hc

/-- The DGS Frattini quotient cannot be irreducible at the tensor endpoint
under the temporary zero-core assumption. -/
theorem old_residual_core_zero_parabolic_core_not_frattini_irreducible
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    ¬ IsNormalizerFrattiniIrreducible (pCore 2 (ChapterF.Source.parabolic
      ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0)) := by
  intro hirr
  obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact m.old_residual_common_sylow_not_le_component
    (hf.a5_local_containment_of_frattini_irreducible hn 0 e hirr)

/-- Either of these literal DGS core profiles closes the original 9.3.3
contradiction. Obtaining the alternative remains the source-branch obligation. -/
theorem old_residual_overgroup_core_ne_bot_of_dgs_core_profile
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hprofile :
      Nat.card (pCore 2 (ChapterF.Source.parabolic
        ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0)) ≤ 256 ∨
      IsNormalizerFrattiniIrreducible (pCore 2 (ChapterF.Source.parabolic
        ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0))) :
    pCore 2 M₀ ≠ ⊥ := by
  intro hzero
  rcases hprofile with hsmall | hirr
  · exact (not_lt_of_ge hsmall) (m.old_residual_core_zero_parabolic_core_card_gt_256
      hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero)
  · exact m.old_residual_core_zero_parabolic_core_not_frattini_irreducible
      hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero hirr

/-- The original field-four consumer, with the oriented DGS core profile explicit. -/
theorem old_residual_overgroup_fourField_models_of_dgs_core_profile
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hlinear : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      (pResidual 2 H).IsCComponent → IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) →
        ¬ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax (T.subtype hH.1.1.2) hP)
          (pResidual 2 H)) 3 4)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hprofile :
      Nat.card (pCore 2 (ChapterF.Source.parabolic
        ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0)) ≤ 256 ∨
      IsNormalizerFrattiniIrreducible (pCore 2 (ChapterF.Source.parabolic
        ![L, (pResidual 2 H).map H.subtype] (commonTwo T L) 0)))
    :
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
  obtain ⟨eK⟩ := m.old_residual_a5_of_no_linear_three_four hH hlarge hlinear
  have hcore := m.old_residual_overgroup_core_ne_bot_of_dgs_core_profile
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hprofile
  exact m.old_residual_overgroup_fourField_models_of_no_linear_three_four
    hH hlarge hlinear houtside M₀ hcore hgen hKU


end CFSG.Quasithin.Chapter10.SourceA5TensorModel
