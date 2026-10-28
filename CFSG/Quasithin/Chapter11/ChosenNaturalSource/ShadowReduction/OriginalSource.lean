module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Source
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceAssembly

/-!
# Shadow reduction on the original quotient from earlier source inputs

The complete compatible-field proof of 11.3.2 is applied to the original
flag and to every reselected module needed in the field-four triangle.
Uniqueness of the marked flag supplies inner uniqueness. If C_V(L) were
nontrivial, its normalizer would contain every quotient-line centralizer;
an outside H then satisfies 11.3.1 and contradicts 11.3.2. Thus the separate
fixed-space premise in the component interface is discharged here.

The component comparison, triangle exclusion, point and line products,
generation-one selection and literal R₁-Sylow argument now assemble without
any shadow, fixed-space, component-equality or endgame hypothesis. The output
retains the original action marking, quotient and one common selected H.

Universal normalized 7.0.1 is supplied in the final application by its checked
conditional source theorem, with 3.2.5 discharged. Its doubled and Mathieu
branch inputs remain with qt-d-1222-nonff-doubled and qt-d-1222-nonff-mathieu.
Odd-kernel normalizer control remains with
qt-d-1222-natural-odd-kernel-normalizer. The §§11.0--11.2 inputs, including
the swapped-module instances, retain qt-d-1222-natural-local-geometry.
Final discharge of these independent inputs remains with
qt-d-1222-natural-shadow-reduction; this conditional application does not
claim completion under preceding geometry alone. The parent
qt-d-1222-nonbinary-natural supplies that geometry to the final assembly.

Source: Aschbacher--Smith, refs/quasithin.pdf, 11.3.1--11.5.1,
printed pp.770--779. G₁ is N_G(V₁), and component normality is relative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

/-- Nontrivial fixed space itself supplies the centralizer clause of 11.3.1.
This removes the separate SL₃ fixed-space input from the 11.4.1 application. -/
theorem fixed_trivial_of_proposition1132 (S : D.NonbinaryNaturalInput)
    (U : Submodule (ZMod 2) D.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S U H → Proposition1132At D S U H) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨H, hH⟩ := exists_outside D S
  have hc : centralizer (D.centralQuotientPreimage U : Set G) ≤
      normalizer (L : Set G) := by
    by_contra hout
    exact hne (fixed_trivial_of_quotient_preimage_centralizer_outside D S U hout)
  exact hne (h1132 H ⟨hH, omega_moves_of_fixed_nontrivial D S hH hne,
    fun _ => hc⟩).fixed_trivial

/-- Apply the complete field and commutator construction to any original
invariant flag; its inner uniqueness is proved from the actual marking. -/
theorem proposition1132_of_preceding_source
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field}
    (f : InvariantFlag c) (H : Subgroup G)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1132 c f H)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  obtain ⟨g, hg, hi, _, _⟩ := exists_unique_marked_flag D S c
  have hu : f.IsInnerUnique := by
    intro i U hdim hnorm
    exact (hi i U hdim hnorm).trans (hg i (f.space i) (f.dimension i) (f.invariant i)).symm
  exact proposition1132_of_normalized_source c f hu s p hcontrol h701

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
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (hcontrol : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      D_J.NonbinaryNaturalInput →
      WeakClosure.Generation.OddKernelNormalizer (T := T) (L := J) (V := W))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Preceding1132 c_J f_J JH)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ActionEquiv D_J.centralQuotientAction (binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z H).K X 0 S.field.degree)
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)

include h hNT hcent hcartan_line hX hXR hKZ h701 hcontrol hpre h1122 href h1115

/-- The original 11.4 output with the complete shadow implication and fixed
space proved before applying the component comparison and triangle exclusion. -/
theorem ofFlag_reduction_of_shadow_geometry : SourceReductionAt (ofFlag S f X z H) := by
  have hs (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH
      (s : Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH) :=
    proposition1132_of_preceding_source S_J f_J JH s
      (hpre J W D_J S_J c_J f_J JH s) (hcontrol J W D_J S_J) h701
  have hf := fixed_trivial_of_proposition1132 S _ (hs L V D S c f)
  exact ComponentGeometry.ofFlag_source_reduction S f X z H h hNT (fun _ => hf)
    hcent hcartan_line hX hXR hKZ (fun J W D_J hJ => h701 J W D_J hJ S.many)
    hs h1122 href h1115 (hcontrol L V D S)

variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- Surviving SL₃/Sp₄ data on the unchanged chosen quotient, with a common
selected H. In the G₂ branch the literal R₁-Sylow construction and E.3.19
are applied internally; no G₂ exclusion or component equality is an input. -/
theorem ofFlag_endgame_of_shadow_geometry :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have r := ofFlag_reduction_of_shadow_geometry S f X z H h hNT hcent hcartan_line
    hX hXR hKZ h701 hcontrol hpre h1122 href h1115
  have hs (J : Subgroup G)
      (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) J) :=
    proposition1132_of_preceding_source S f J s (hpre L V D S c f J s)
      (hcontrol L V D S) h701
  obtain ⟨hall, J, hJ⟩ := endgame_of_component_sources S f X z H h r.refinement r.comparison
    hNT (fun _ => r.fixed_trivial) hs (hcontrol L V D S) h1115
    hunique hthree hline hcomponent
  exact ⟨hall, J, hJ, r.radical, r.commutator⟩

/-- Source 11.5.1 excludes every G₂ marking of this same actual quotient.
The local parameter compares markings without replacing the original action. -/
theorem ofFlag_not_g2_of_shadow_geometry :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction (binaryG2 S.field)) := by
  obtain ⟨_, J, e, _, _⟩ := ofFlag_endgame_of_shadow_geometry S f X z H h hNT
    hcent hcartan_line hX hXR hKZ h701 hcontrol hpre h1122 href h1115
    hunique hthree hline hcomponent
  rintro ⟨m⟩
  have hg := WeakClosure.Parameters.localM_eq_naturalParameter D S (.g2 m)
  have he := e.local_parameter
  change @ChapterE.localM G _ V D.elementary = S.field.degree at he
  change @ChapterE.localM G _ V D.elementary = 2 * S.field.degree at hg
  have hn := S.nonbinary
  omega

omit h701 in
/-- Actual normalized-source application: 3.2.5 is proved on each selected
module, including the swapped triangle. The two non-FF branch implications
and odd-kernel control are the remaining independently owned source inputs.
The result includes the marked G₂ exclusion and the SL₃/Sp₄ closure data. -/
theorem ofFlag_shadow_reduction_of_normalized_branches
    (hdoubled : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      D_J.MarkedDoubled → ¬ IsFFModule D_J.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      W = D_J.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D_J.orbitRepresentation D_J.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient D_J.orbitComponent →
      ¬ IsFFModule D_J.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    (¬ Nonempty (ActionEquiv D.centralQuotientAction (binaryG2 S.field))) ∧
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hn (J W : Subgroup G) (D_J : ChosenModule T J W)
      (hJ : Hypothesis1223 KnownSimple.IsKnownSimple T J)
      (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :=
    D_J.sourceOrbit_alternatives_of_source_inputs_of_many hJ hmany
      (D_J.source325_of_many hJ hmany) (hdoubled J W D_J hJ hmany)
      (hmathieu J W D_J hJ hmany)
  exact ⟨ofFlag_not_g2_of_shadow_geometry S f X z H h hNT hcent hcartan_line
      hX hXR hKZ hn hcontrol hpre h1122 href h1115 hunique hthree hline hcomponent,
    ofFlag_endgame_of_shadow_geometry S f X z H h hNT hcent hcartan_line
      hX hXR hKZ hn hcontrol hpre h1122 href h1115 hunique hthree hline hcomponent⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
