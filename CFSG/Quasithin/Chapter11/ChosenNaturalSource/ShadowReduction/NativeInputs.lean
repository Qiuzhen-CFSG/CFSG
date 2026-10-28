module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.OriginalInputs

/-!
# Shadow reduction with the fixed native J₄ locals

The embedded third local is the proved native normalizer M_F. Its full
intrinsic two-core quotient identifies it with L₅(2), so the shadow reduction
no longer needs an independently supplied third local or quotient marking.
The cover still concerns the whole normalizer of each nontrivial elementary
subgroup of the actual J₄ carrier.

The doubled and Mathieu non-FF implications and uniform native cover remain
explicit, owned by qt-d-1222-nonff-doubled, qt-d-1222-nonff-mathieu, and
qt-model-j4-elementary-normalizer-cover. Preceding geometry, including its
reselected-module instances, retains its source owners. Final discharge stays
with qt-d-1222-natural-shadow-reduction and qt-d-1222-nonbinary-natural.

The final theorem feeds the original 11.5.3 closure consumer using the same
selected outside subgroup and actual quotient. Source: Aschbacher--Smith,
refs/quasithin.pdf, 11.3.1--11.5.3, printed pp.770--780; Kleidman--Wilson
(1988), Section 2, for the native elementary-normalizer cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open WeakClosure.Generation.OddNormalizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

variable
    (hcover : NativeElementaryNormalizerCover Janko4.LocalStructure.LinearFive.M_F)
    (hdoubled : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      E.MarkedDoubled → ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (J W : Subgroup G) (E : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      W = E.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient E.orbitComponent →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))

include hcover hdoubled hmathieu


variable (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hcent : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G))
    (hcartan_line : f.Vi 0 = ⁅zpowers z, X⁆)
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : (ofFlag S f X z H).K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (hpre : ∀ (J W : Subgroup G) (E : ChosenModule T J W)
      (S_J : E.NonbinaryNaturalInput) (c_J : Coordinates E S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At E S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Preceding1132 c_J f_J JH)
    (h1122 : ∀ (J W : Subgroup G) (E : ChosenModule T J W)
      (S_J : E.NonbinaryNaturalInput),
      Nonempty (ActionEquiv E.centralQuotientAction (binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W E.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z H).K X 0 S.field.degree)
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)

include h hNT hcent hcartan_line hX hXR hKZ hpre h1122 href h1115


variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- The complete conditional shadow/G₂ reduction uses the fixed native
third local and its proved intrinsic quotient. -/
theorem ofFlag_shadow_reduction_of_native_cover :
    SourceReductionAt (ofFlag S f X z H) ∧
    (¬ Nonempty (ActionEquiv D.centralQuotientAction (binaryG2 S.field))) ∧
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  ofFlag_shadow_reduction_of_elementary_cover Janko4.LocalStructure.LinearFive.M_F
    (Janko4.LocalStructure.LinearFive.M_F_intrinsicQuotient.trans
      Representation.SL5TenDimensional.projectiveEquiv) hcover hdoubled hmathieu
    S f X z H h hNT hcent hcartan_line hX hXR hKZ hpre h1122 href h1115
    hunique hthree hline hcomponent

/-- The same selected outside subgroup supplies the actual nonabelian
closure consequence. The earlier 11.2.5 obstruction remains explicit. -/
theorem ofFlag_selected_nonabelian_of_native_cover
    (hweak : ∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) →
      Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) J) :
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ((ofFlag S f X z J).K = f.Li 0 →
        ¬ IsMulCommutative (ofFlag S f X z J).W) := by
  obtain ⟨_, _, _, J, e, hr, hc⟩ :=
    ofFlag_shadow_reduction_of_native_cover hcover hdoubled hmathieu S f X z H
      h hNT hcent hcartan_line hX hXR hKZ hpre h1122 href h1115
      hunique hthree hline hcomponent
  exact ⟨J, e, hr, hc, e.nonabelian_of_component_eq (hweak J e.outside e.inside_point)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
