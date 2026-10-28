module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairSource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreRecognition

/-!
# Full reduced catalogue at the original tensor pair

Use exactly the pair constructed by old_residual_core_zero_rank_two_source.
Its two original A5 quotient markings, Borel normalizations and generated
quasithinness apply the complete catalogue implication. Both original
join-core equalities and containments follow, contradicting the original
failure S ≤ L. This proves nonzero overgroup core and supplies the actual
field-four tensor application with the original KnownSimple/proper-K scope.

The earlier partial row applications are retained. The final two exports
require only the genuine full reduced catalogue; every model marking,
local core calculation and row exclusion has been discharged. Genuine
source selection remains with qt-dgs85-source-assembly, and unconditional
assembly remains with qt-d-tensor-a5-amalgam.

Source: Aschbacher–Smith 9.3.3, p.733, and F.1.12, pp.262–264;
DGS (15.2)–(15.3), pp.226–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 SourceOldResidualOvergroup
open Chapter4 ChapterB ChapterE ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
open ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The genuine reduced linear or symplectic row closes the original zero-overgroup-core contradiction. -/
theorem old_residual_overgroup_core_ne_bot_of_reduced_linear_or_symplectic
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
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hnF : 0<n) (point : Bool)
    (er : Nonempty (RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
        ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
      (ChapterF.Source.DGS85.OriginalExtension.LinearNative.amalgam F point)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
          ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
        (ChapterF.Source.DGS85.OriginalExtension.SymplecticNative.amalgam F point)))
    : pCore 2 M₀ ≠ ⊥ := by
  intro hzero
  obtain ⟨hf,hqt,hq,hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  apply m.old_residual_common_sylow_not_le_component
  rcases er with er | er
  · exact (ChapterF.Source.A5PairCatalogue.linear_core_and_containment
      hf hq ⟨0,hn 0⟩ F hF hnF point er.some).2 0
  · exact (ChapterF.Source.A5PairCatalogue.Symplectic.core_and_containment
      F hf hq ⟨0,hn 0⟩ hF hnF point er.some).2 0

/-- The original field-four tensor consumer, conditional only on the genuine reduced linear or symplectic row. -/
theorem old_residual_overgroup_fourField_models_of_reduced_linear_or_symplectic
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
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hnF : 0<n) (point : Bool)
    (er : Nonempty (RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
        ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
      (ChapterF.Source.DGS85.OriginalExtension.LinearNative.amalgam F point)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
          ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
        (ChapterF.Source.DGS85.OriginalExtension.SymplecticNative.amalgam F point)))
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
  have hcore := m.old_residual_overgroup_core_ne_bot_of_reduced_linear_or_symplectic
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen F hF hnF point er
  exact m.old_residual_overgroup_fourField_models_of_no_linear_three_four
    hH hlarge hlinear houtside M₀ hcore hgen hKU

/-- At the literal old-residual tensor pair, the full reduced catalogue leaves
only the five undischarged regular rows if the overgroup core vanishes. -/
theorem old_residual_overgroup_core_or_remaining_of_reduced_catalogue
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
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      L ((pResidual 2 H).map H.subtype) (commonTwo T L)) :
    pCore 2 M₀ ≠ ⊥ ∨ ChapterF.Source.A5PairCatalogue.RemainingReducedRows
      L ((pResidual 2 H).map H.subtype) (commonTwo T L) := by
  classical
  by_cases hzero : pCore 2 M₀ = ⊥
  · obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
      hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
    rcases ChapterF.Source.A5PairCatalogue.core_and_containment_or_remaining
      hf hq ⟨0,hn 0⟩ ha with ⟨_,hS⟩ | hr
    · exact (m.old_residual_common_sylow_not_le_component (hS 0)).elim
    · exact Or.inr hr
  · exact Or.inl hzero

/-- The full reduced catalogue at the literal tensor pair leaves only G2
when the original overgroup core vanishes. Both original A5 marks, the full
Borel, and quasithinness of this generated pair are supplied by 9.3.3. -/
theorem old_residual_overgroup_core_or_reduced_g2
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
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      L ((pResidual 2 H).map H.subtype) (commonTwo T L)) :
    pCore 2 M₀ ≠ ⊥ ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (short : Bool),
        Nonempty (RankTwoAmalgam.Iso
          (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
            ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
          (ChapterF.Source.DGS85.OriginalExtension.G2Native.amalgam F short)) := by
  classical
  by_cases hzero : pCore 2 M₀ = ⊥
  · obtain ⟨hf, hqt, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
      hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
    rcases ChapterF.Source.A5PairCatalogue.core_and_containment_or_g2
      hf hqt hq ⟨0,hn 0⟩ ha with ⟨_,hS⟩ | hr
    · exact (m.old_residual_common_sylow_not_le_component (hS 0)).elim
    · exact Or.inr hr
  · exact Or.inl hzero

/-- The actual field-four tensor application under the full reduced catalogue.
Only the surviving G2 comparison remains as an alternative to its conclusion. -/
theorem old_residual_overgroup_fourField_models_or_reduced_g2
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
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      L ((pResidual 2 H).map H.subtype) (commonTwo T L))
    :
    (m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
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
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (short : Bool),
        Nonempty (RankTwoAmalgam.Iso
          (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam
            ![L,(pResidual 2 H).map H.subtype] (commonTwo T L))
          (ChapterF.Source.DGS85.OriginalExtension.G2Native.amalgam F short)) := by
  obtain ⟨eK⟩ := m.old_residual_a5_of_no_linear_three_four hH hlarge hlinear
  rcases m.old_residual_overgroup_core_or_reduced_g2
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen ha with hcore | hg2
  · exact Or.inl (m.old_residual_overgroup_fourField_models_of_no_linear_three_four
      hH hlarge hlinear houtside M₀ hcore hgen hKU)
  · exact Or.inr hg2

/-- At the literal 9.3.3 pair, the full genuine reduced catalogue discharges
all row-specific premises of the original nonzero-overgroup-core argument. -/
theorem old_residual_overgroup_core_ne_bot_of_reduced_catalogue
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
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      L ((pResidual 2 H).map H.subtype) (commonTwo T L)) :
    pCore 2 M₀ ≠ ⊥ := by
  intro hzero
  obtain ⟨hf,hqt,hq,hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact m.old_residual_common_sylow_not_le_component
    ((ChapterF.Source.a5_pair_core_and_containment_of_reduced_catalogue
      hf hqt hq ⟨0,hn 0⟩ ha).2 0)

/-- The actual field-four tensor application, conditional only on the
earlier reduced catalogue for the original pair. The original KnownSimple
and proper-K hypotheses are retained in FundamentalSetup. -/
theorem old_residual_overgroup_fourField_models_of_reduced_catalogue
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
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      L ((pResidual 2 H).map H.subtype) (commonTwo T L))
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
  have hcore := m.old_residual_overgroup_core_ne_bot_of_reduced_catalogue
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen ha
  exact m.old_residual_overgroup_fourField_models_of_no_linear_three_four
    hH hlarge hlinear houtside M₀ hcore hgen hKU

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
