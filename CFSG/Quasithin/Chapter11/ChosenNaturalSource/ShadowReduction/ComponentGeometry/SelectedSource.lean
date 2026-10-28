module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.MarkedSource

/-!
# Selected component outputs before the terminal G₂ contradiction

The component reduction selects the same outside H used by the final argument.
For a classical marking it supplies the actual marked endgame, including both
section-centralizer products and the O²(H) alternative. For a G₂ marking it
constructs H₁ = R₁O²(H), with its ambient R₁-Sylow image, escape and generation
one. This selection does not use the terminal E.3.19 contradiction.

The final applications discharge OddKernelNormalizer using the checked uniform
elementary-normalizer-cover implication, including the full SL₃(4) cover. Its
native J₄ cover and embedded third-local quotient remain independent inputs of
qt-d-1222-natural-odd-kernel-normalizer through
qt-d-1222-shadow-component-witness. No ordinary full-module callback remains.
The preceding geometry and full Proposition1132At implication retain final
discharge with qt-d-1222-natural-shadow-reduction. In particular these conditional
applications do not assert that the independent cover has been established.

Source: Aschbacher–Smith, refs/quasithin.pdf, 11.4.1–4 and the construction in
11.5.1, printed pp.775–779. G₁ is N_G(V₁); all normality is relative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

/-- Output of the G₂ selection, before applying E.3.19. The marking is on the
original quotient, and the witness retains its actual Sylow and embedding. -/
structure SelectedG2At (E : Closure.Geometry D) : Prop where
  marking : Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
    (ChapterB.QuasisimpleSource.binaryG2 E.input.field))
  outside : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M
  inside_point : E.H ≤ Gz E
  residual : SelectedResidualAlternative E
  generation_one : ChapterE.generationParameter E.H = 1
  radical_witness : ∃ w : OutsideRadicalWitness E,
    w.H₁ = E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype

private theorem endgame_of_selected {E : Closure.Geometry D}
    (r : SourceReductionAt E) (a : Closure.Nonabelian.MarkedFlag E)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHz : E.H ≤ Gz E) (hres : SelectedResidualAlternative E)
    (hn : ChapterE.generationParameter E.H = 1) : EndgameAt E :=
  ⟨⟨a⟩, r.fixed_trivial, r.transitive, hz, hz1, r.comparison,
    r.line_component, r.point_component, r.refinement, hH, hHz, hres, hn,
    local_parameter_of_markedFlag a, r.point_product, r.line_product⟩

variable (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (hcent : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G))
    (hcartan_line : f.Vi 0 = ⁅zpowers z, X⁆)
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : (ofFlag S f X z H).K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h1132 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z H).K X 0 S.field.degree)
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)

include h hNT hlinear hcent hcartan_line hX hXR hKZ h701 h1132 h1122 href h1115

/-- The complete original component reduction, including the full SL₃(4)
row, under the independent native cover theorem. The ordinary full-module
premise and odd-kernel normalizer callback have both been discharged. -/
theorem ofFlag_source_reduction_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : WeakClosure.Generation.OddNormalizer.NativeElementaryNormalizerCover C) :
    SourceReductionAt (ofFlag S f X z H) := by
  exact ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_elementary_cover D S C eC hcover)

variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- Construct the actual selected H on every marking. The classical branch
retains the unchanged marked quotient; the G₂ branch supplies the outside
R₁-Sylow subgroup for the parent's terminal E.3.19 application. -/
theorem ofFlag_selected_source
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ J, SourceReductionAt (ofFlag S f X z J) ∧
      (EndgameAt (ofFlag S f X z J) ∨ SelectedG2At (ofFlag S f X z J)) := by
  have r := ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115 hcontrol
  have reselect (J : Subgroup G) : SourceReductionAt (ofFlag S f X z J) :=
    ⟨r.fixed_trivial, r.transitive, r.comparison, r.line_component, r.point_component,
      r.refinement, r.radical, r.commutator, r.point_product, r.line_product,
      r.equality_escape, r.generation_one, r.selected⟩
  cases c with
  | sl3 m =>
    obtain ⟨J, hJ, hJz, hres, hn⟩ := r.selected
    exact ⟨J, reselect J, Or.inl (endgame_of_selected (reselect J) ⟨.sl3 m, f, rfl, rfl, rfl⟩
      h.point_mem h.point_ne_one hJ hJz hres hn)⟩
  | sp4 m =>
    obtain ⟨J, hJ, hJz, hres, hn⟩ := r.selected
    exact ⟨J, reselect J, Or.inl (endgame_of_selected (reselect J) ⟨.sp4 m, f, rfl, rfl, rfl⟩
      h.point_mem h.point_ne_one hJ hJz hres hn)⟩
  | g2 m =>
    obtain ⟨J, hJ, hJz, hres, hn, w, hw⟩ :=
      ofFlag_g2_source_witness_of_preceding S f X z H h hNT hlinear hcent hcartan_line
        hX hXR hKZ h701 h1132 h1122 href h1115 hunique hthree hline hcomponent m rfl
    exact ⟨J, reselect J, Or.inr ⟨⟨m⟩, hJ, hJz, hres, hn, w, hw⟩⟩

/-- Apply the independent native cover to the full selected-source family.
All component comparison, triangle, generation and Sylow conclusions are
constructed; only the registered preceding sources and native cover remain. -/
theorem ofFlag_selected_source_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : WeakClosure.Generation.OddNormalizer.NativeElementaryNormalizerCover C) :
    ∃ J, SourceReductionAt (ofFlag S f X z J) ∧
      (EndgameAt (ofFlag S f X z J) ∨ SelectedG2At (ofFlag S f X z J)) := by
  exact ofFlag_selected_source S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115 hunique hthree hline hcomponent
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_elementary_cover D S C eC hcover)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
