module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.OriginalSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source

/-!
# Original shadow reduction from the concrete elementary-normalizer cover

The concrete J4 elementary-normalizer cover supplies odd-kernel control for
all chosen natural modules needed by the shadow argument, including the full
SL3(4) central cover. The ordinary full-module case has already been proved
by its producer. The doubled and Mathieu source exits, together with source
3.2.5 and the completed non-Mathieu theorem, supply normalized 7.0.1 at each
selected overcomponent. These results apply also to the reselected module
in the field-four triangle.

The application below constructs the fixed-space, component, local-product
and generation-one conclusions. The G2 branch is eliminated using the literal
R1-Sylow outside subgroup and E.3.19, and the surviving SL3/Sp4 data use one
common selected H. A final application feeds the original 11.5.3 closure
consumer, with the exact preceding 11.2.5 obstruction left explicit.

The independent inputs still owed are the doubled and Mathieu source exits
(qt-d-1222-nonff-doubled and qt-d-1222-nonff-mathieu) and the native elementary
normalizer cover with its actual third-local quotient
(qt-model-j4-elementary-normalizer-cover). This is conditional progress,
not completion from preceding geometry alone. Final discharge stays with
qt-d-1222-natural-shadow-reduction; its parent supplies the preceding
geometry, and qt-d-1222-natural-closure consumes the endgame. No shadow,
fixed-space, component-equality or endgame conclusion is a source input.

Source: Aschbacher--Smith, refs/quasithin.pdf, 7.0.1 and 11.3.1--11.5.3,
printed pp.695,770--780. G1 = N_G(V1); component normality is relative.
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
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
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

include eC hcover hdoubled hmathieu


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

/-- Full downstream application on the unchanged D quotient. The component
output retains both relative normality statements and both products. The same
selected outside J carries the surviving marked flag and radical bounds.
The G2 contradiction uses the constructed R1-Sylow subgroup and E.3.19. -/
theorem ofFlag_shadow_reduction_of_elementary_cover :
    SourceReductionAt (ofFlag S f X z H) ∧
    (¬ Nonempty (ActionEquiv D.centralQuotientAction (binaryG2 S.field))) ∧
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hn (J W : Subgroup G) (E : ChosenModule T J W)
      (hJ : Hypothesis1223 KnownSimple.IsKnownSimple T J)
      (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :=
    E.sourceOrbit_alternatives_of_source_inputs_of_many hJ hmany
      (E.source325_of_many hJ hmany) (hdoubled J W E hJ hmany) (hmathieu J W E hJ hmany)
  have hc (J W : Subgroup G) (E : ChosenModule T J W) (S_J : E.NonbinaryNaturalInput) :=
    oddKernelNormalizer_of_elementary_cover E S_J C eC hcover
  have r := ofFlag_reduction_of_shadow_geometry S f X z H h hNT hcent hcartan_line
    hX hXR hKZ hn hc hpre h1122 href h1115
  have hs (J : Subgroup G)
      (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) J) :=
    proposition1132_of_preceding_source S f J s (hpre L V D S c f J s)
      (hc L V D S) hn
  obtain ⟨hall, J, e⟩ := endgame_of_component_sources S f X z H h r.refinement r.comparison
    hNT (fun _ => r.fixed_trivial) hs (hc L V D S) h1115
    hunique hthree hline hcomponent
  have hnot : ¬ Nonempty (ActionEquiv D.centralQuotientAction (binaryG2 S.field)) := by
    rintro ⟨m⟩
    have hg := WeakClosure.Parameters.localM_eq_naturalParameter D S (.g2 m)
    have he := e.local_parameter
    change @ChapterE.localM G _ V D.elementary = S.field.degree at he
    change @ChapterE.localM G _ V D.elementary = 2 * S.field.degree at hg
    have hn := S.nonbinary
    omega
  exact ⟨r, hnot, hall, J, e, r.radical, r.commutator⟩

/-- Apply the surviving source data to the first closure theorem. For the
same selected outside J, equality with the original rank-one component forces
the actual normal closure of V in N_G(V1) to be nonabelian. Only the earlier
11.2.5 obstruction is supplied to this consumer; none of its shadow inputs
or the local generation parameter is assumed. -/
theorem ofFlag_selected_nonabelian_of_elementary_cover
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
    ofFlag_shadow_reduction_of_elementary_cover C eC hcover hdoubled hmathieu S f X z H
      h hNT hcent hcartan_line hX hXR hKZ hpre h1122 href h1115
      hunique hthree hline hcomponent
  exact ⟨J, e, hr, hc, e.nonabelian_of_component_eq (hweak J e.outside e.inside_point)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
