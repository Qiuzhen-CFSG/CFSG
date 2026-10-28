module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.G2Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.OddBlock
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Complete

/-!
# The original marked endgame after the shadow and component proofs

The G₂ branch is eliminated by constructing the literal R₁-Sylow outside
subgroup and applying E.3.19. The other branches retain their original
action marking and flag. The same selected H has generation parameter one,
the O²(H) alternative, and both point and line products. These data feed
the actual 11.5.3 nonabelianness theorem, with its fixed-space, transitivity,
local-parameter and generation hypotheses discharged here.

This is assembly, not a proof of the two still explicit source inputs:
full Proposition1132At belongs to qt-d-1222-shadow-linear-geometry, and
K(V,z)=K(V,V₁) belongs to qt-d-1222-shadow-components. The earlier geometry
and odd-kernel control retain their existing producers. Final discharge
remains with qt-d-1222-natural-shadow-reduction. In particular the output
record is never assumed as a source hypothesis.

Source: Aschbacher--Smith, refs/quasithin.pdf, 11.4.1--11.5.3,
printed pp.775--780. G₁ throughout is N_G(V₁), and all normality is relative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

/-- Output on the original chosen quotient, with one common selected H.
No existence assertion is implicit in this specification. -/
structure EndgameAt (E : Closure.Geometry D) : Prop where
  marked_flag : Nonempty (Closure.Nonabelian.MarkedFlag E)
  fixed_trivial : V ⊓ centralizer (L : Set G) = ⊥
  transitive : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
    ∃ l ∈ L, (MulAut.conj l) u = v
  point_mem : E.z ∈ E.V₁
  point_ne_one : E.z ≠ 1
  comparison : E.Kz = E.K
  line_component : Source.NormalComponentIn E.G₁ E.K
  point_component : Source.NormalComponentIn (Gz E) E.K
  refinement : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree
  outside : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M
  inside_point : E.H ≤ Gz E
  residual : SelectedResidualAlternative E
  generation_one : ChapterE.generationParameter E.H = 1
  local_parameter : @ChapterE.localM G _ V D.elementary = E.input.field.degree
  point_product : ∀ g ∈ Gz E, ∃ k ∈ E.K, ∃ y ∈ Yz E,
    ∃ m ∈ Mz E, g = k * y * m
  line_product : ∀ g ∈ E.G₁, ∃ k ∈ E.K, ∃ y ∈ E.Y,
    ∃ m ∈ E.M₁, g = k * y * m

/-- The surviving marking computes the local parameter on the original V;
no identification of the full module with its quotient is assumed. -/
theorem local_parameter_of_markedFlag {E : Closure.Geometry D}
    (a : Closure.Nonabelian.MarkedFlag E) :
    @ChapterE.localM G _ V D.elementary = E.input.field.degree := by
  have hm := WeakClosure.Parameters.localM_eq_naturalParameter D E.input a.action.coordinates
  cases ha : a.action <;>
    simpa only [ha, Closure.Nonabelian.RemainingAction.coordinates,
      WeakClosure.Parameters.naturalParameter] using hm

/-- Assemble the actual surviving flag, selected outside H and source products.
The explicit later-source inputs are 11.3.2, the surviving component list,
and 11.4.2. The next theorem discharges the list using the full 11.1.2 input. -/
theorem endgame_of_component_sources
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1)) :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) := by
  have hmark (J : Subgroup G) : Nonempty (Closure.Nonabelian.MarkedFlag (ofFlag S f X z J)) := by
    cases c with
    | sl3 m => exact ⟨⟨.sl3 m, f, rfl, rfl, rfl⟩⟩
    | sp4 m => exact ⟨⟨.sp4 m, f, rfl, rfl, rfl⟩⟩
    | g2 m =>
      exact (Outside.ofFlag_g2_impossible_from_preceding S m f X z H h hcase he
        hNT hlinear h1132 hcontrol hunique hthree hline hcomponent).elim
  obtain ⟨hf, ht⟩ := fixed_and_transitive D S _ hlinear h1132
  obtain ⟨hall, J, hJ, hJz, hres, hn⟩ :=
    Outside.Generation.ofFlag_selected_and_universal_generation_one S f X z H h hcase he
      hNT hlinear h1132 hcontrol h1115
  obtain ⟨hprod, hprod'⟩ := Outside.Models.ofFlag_surviving_products S f X z H
    h hcase he hNT hlinear h1132
  have hnormal := (point_component_relative_normal (ofFlag S f X z H)
    h.seed_centralizes h.point_mem).2
  refine ⟨hall, J, ⟨hmark J, hf, ht, h.point_mem, h.point_ne_one, he,
    ⟨h.line_component, (ofFlag S f X z J).K_relative_normal⟩,
    ?_, hcase, hJ, hJz, hres, hn, local_parameter_of_markedFlag (hmark J).some,
    hprod, hprod'⟩⟩
  exact ⟨he ▸ h.point_component, he ▸ hnormal⟩

/-- Discharge the entire field-four triangle and the radical bounds before
constructing the surviving endgame. Only 11.3.2 and 11.4.2 remain as
later-source inputs; the other hypotheses are the registered preceding
geometry and recognition implications, including their swapped-I instances. -/
theorem endgame_of_preceding_and_shadow_sources
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hX : X ≤ normalizer (f.Vi 0 : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (hKZ : (ofFlag S f X z H).K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h325 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J → D_J.Source325Alternatives)
    (h1132 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) H,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) H →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) H)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
      (ofFlag S f X z H).K X 0 S.field.degree) :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨hc, hrad, hcomm⟩ := Radical.ofFlag_refinement_and_bounds_of_preceding_sources
    D S f (ofFlag S f X z H).K X z H
    ⟨h.line_component, (ofFlag S f X z H).K_relative_normal⟩
    h.line_component_centralizes (le_conjugateSpanBy _ _) hX hXR hKZ
    h701 h325 h1132 h1122 href
  obtain ⟨hall, J, hJ⟩ := endgame_of_component_sources S f X z H h hc he hNT hlinear
    (h1132 L V D S c f) hcontrol h1115 hunique hthree hline hcomponent
  exact ⟨hall, J, hJ, hrad, hcomm⟩

/-- The first actual closure consumer: all shadow conclusions and the local
parameter are supplied by the assembled endgame. The only extra geometric
input is the preceding 11.2.5 obstruction for this same selected H. -/
theorem EndgameAt.nonabelian_of_component_eq {E : Closure.Geometry D}
    (e : EndgameAt E)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H) :
    E.K = E.L₁ → ¬ IsMulCommutative E.W :=
  Closure.Nonabelian.not_isMulCommutative_of_K_eq e.marked_flag.some e.fixed_trivial
    (WeakClosure.seed_normalizer_le D E.input)
    e.point_mem e.point_ne_one e.transitive e.comparison
    (Preliminary.seed_ti D E.input) e.outside hweak e.local_parameter e.generation_one

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
