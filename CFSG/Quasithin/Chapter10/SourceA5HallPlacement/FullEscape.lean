module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceAssembly
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Complete
/-!
# The original Hall placement after full normalizer escape

The complete 4.4.13(1) source proof discharges the Hall-kernel escape premise
in the original A₅ placement. The independent component-normalizer conclusion
of 4.4.3 remains explicit; no full-Hall or selected-torus substitute is assumed.
Source: Aschbacher–Smith 4.4.13(1), 4.4.3, and 10.2.1.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual Hall witness is faithful from the proved full-Hall escape
and the independent component-normalizer control. Its inclusion, Hall property and ambient image are literal. -/
theorem source_a5_hstar_hall_faithful_of_component_normalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  exact source_a5_hstar_hall_faithful_of_oddNormalizer_control
    D e hn ht htn hcoords (NormalizerEscape.source4413One_knownSimple G) hcontrol hH hlarge

/-- The separated original source generation bound now requires only
the independent nonnormal-pair normalizer conclusion of 4.4.3. -/
theorem source_a5_hstar_generation_bound_of_component_normalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H ≤ 2 := by
  exact source_a5_hstar_generation_bound_of_oddNormalizer_control
    D e hn ht htn hD hbound hsep (NormalizerEscape.source4413One_knownSimple G) hcontrol hH
local instance fullEscapeAssemblyMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance fullEscapeAssemblyFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The separated original source reaches its natural weak-closure endpoint
from the complete full-Hall escape and independent component-normalizer control. -/
theorem source_a5_natural_and_parameters_eq_two_of_component_normalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  exact source_a5_natural_and_parameters_eq_two_of_oddNormalizer_control
    D e hn ht htn hD hbound hsep (NormalizerEscape.source4413One_knownSimple G) hcontrol hcent hH
end CFSG.Quasithin.Chapter10
