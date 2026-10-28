module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan

/-!
# Original component reduction and its selected outside subgroup

Apply the full component comparison and the canonical triangle/radical theorem
on the same chosen flag. Its rank-one quotient marking comes from uniqueness
of the marked flag. The original multiple-overgroup hypothesis supplies source
3.2.5, and the original no-J4 hypothesis removes the J4 branch of 7.0.1 in the
comparison. Thus neither component equality nor a model-quotient witness is an
input to this assembly.

The resulting literal point and line products, including the equal-component
escape clause, give generation one for every outside H in the point centralizer
and select H with its O²(H) alternative. In the marked G₂ branch the existing
construction gives H₁ = R₁O²(H), its actual Sylow subgroup, escape and generation
one. A separate application connects the result to the surviving marked endgame.

The remaining hypotheses are the registered preceding geometry, the complete
11.1.2 and 11.1.5 alternatives, normalized 7.0.1, full Proposition1132At (also
for the swapped component), and the original odd-kernel normalizer control.
Their final discharge belongs to qt-d-1222-natural-shadow-reduction through
its existing producers. The conditional comparison and outside-witness families
retain their owners qt-d-1222-shadow-component-comparison and
qt-d-1222-shadow-component-witness; this assembly does not discharge an unfinished
producer merely by applying its conditional theorem.

G₁ is N_G(V₁). All component normality is relative, and both centralizer factors
use the actual action on K/O₂(K). The optional Fitting-index bound is unused.
Source: Aschbacher–Smith, refs/quasithin.pdf, 11.4.1–4 and 11.5.1,
printed pp.775–779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

/-- Output of the original 11.4 reduction. This is never a source assumption. -/
structure SourceReductionAt (E : Closure.Geometry D) : Prop where
  fixed_trivial : V ⊓ centralizer (L : Set G) = ⊥
  transitive : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
    ∃ l ∈ L, (MulAut.conj l) u = v
  comparison : E.Kz = E.K
  line_component : Source.NormalComponentIn E.G₁ E.K
  point_component : Source.NormalComponentIn (Gz E) E.K
  refinement : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree
  radical : E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
    (E.K ⊔ (T : Subgroup G)).subtype
  commutator : ⁅E.R₁, E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2
  point_product : ∀ g ∈ Gz E, ∃ k ∈ E.K, ∃ y ∈ Yz E,
    ∃ m ∈ Mz E, g = k * y * m
  line_product : ∀ g ∈ E.G₁, ∃ k ∈ E.K, ∃ y ∈ E.Y,
    ∃ m ∈ E.M₁, g = k * y * m
  equality_escape : E.K = E.L₁ → ¬ Yz E ≤ E.M
  generation_one : ∀ J, J ∈ Chapter3.HStar (T : Subgroup G) E.M →
    J ≤ Gz E → ChapterE.generationParameter J = 1
  selected : ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ J ≤ Gz E ∧
    (⁅E.K, (pResidual 2 J).map J.subtype⁆ ≤ E.K.pCoreIn 2 ∨
      (pResidual 2 J).map J.subtype ≤ E.K) ∧ ChapterE.generationParameter J = 1

private theorem first_quotient_marking (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* PSL(2,S.field.Carrier)) := by
  obtain ⟨f₀, hu, _, hq, _⟩ := exists_unique_marked_flag D S c
  have hv : f.Vi 0 = f₀.Vi 0 :=
    congrArg c.preimage (hu 0 (f.space 0) (f.dimension 0) (f.invariant 0))
  change Nonempty ((localResidual L (f.Vi 0) ⧸ pCore 2 (localResidual L (f.Vi 0))) ≃*
    PSL(2,S.field.Carrier))
  rw [hv]
  exact hq 0

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
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))

include h hNT hlinear hcent hcartan_line hX hXR hKZ h701 h1132 h1122 href h1115 hcontrol

/-- Source 11.4.1–4 on the original flag, including the source-selected H.
The comparison, fixed space, radical bounds, products and generation are proved
from their preceding inputs; none is assumed as a local callback. -/
theorem ofFlag_source_reduction : SourceReductionAt (ofFlag S f X z H) := by
  have hs := h1132 L V D S c f
  have hf := fixed_and_transitive D S _ hlinear hs
  have h325 (J W : Subgroup G) (D_J : ChosenModule T J W)
      (hJ : Hypothesis1223 KnownSimple.IsKnownSimple T J) : D_J.Source325Alternatives :=
    D_J.source325_of_many hJ S.many
  have hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ J : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D_J : ChosenModule T J W),
        IsFFModule D_J.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D_J.orbitRepresentation
            D_J.orbitComponent := by
    intro _ J hJ W D_J
    exact (h701 J W D_J hJ).imp_right (fun hr => hr.resolve_right hJ.no_J4)
  obtain ⟨e⟩ := first_quotient_marking S f
  have he := Comparison.ofFlag_eq_of_positive_source S f X z H h hlinear hs
    hcent hcartan_line hXR e hpositive h1115
  have hn : Source.NormalComponentIn (ofFlag S f X z H).G₁ (ofFlag S f X z H).K :=
    ⟨h.line_component, (ofFlag S f X z H).K_relative_normal⟩
  obtain ⟨hc, hr, hcomm⟩ := Radical.ofFlag_refinement_and_bounds_of_preceding_sources
    D S f (ofFlag S f X z H).K X z H hn h.line_component_centralizes
    (le_conjugateSpanBy _ _) hX hXR hKZ h701 h325 h1132 h1122 href
  obtain ⟨hp, hl⟩ := Outside.Models.ofFlag_surviving_products S f X z H h hc he hNT hlinear hs
  have hout := Outside.kernel_outside_of_equal (ofFlag S f X z H) h he hNT
    (Outside.Models.ofFlag_surviving_outer_twoClosed S f X z H h hc) hs
  obtain ⟨hall, J, hJ, hJz, hres, hgen⟩ :=
    Outside.Generation.ofFlag_selected_and_universal_generation_one S f X z H h hc he
      hNT hlinear hs hcontrol h1115
  have hpn := (point_component_relative_normal (ofFlag S f X z H)
    h.seed_centralizes h.point_mem).2
  exact ⟨hf.1, hf.2, he, hn, ⟨he ▸ h.point_component, he ▸ hpn⟩,
    hc, hr, hcomm, hp, hl, hout, hall, J, hJ, hJz, hres, hgen⟩

variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- The marked G₂ branch constructs H₁ and an actual Sylow subgroup with
ambient image R₁. This output stops before the terminal E.3.19 contradiction. -/
theorem ofFlag_g2_source_witness
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S.field))
    (hm : c = .g2 m) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype := by
  subst c
  have r := ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115 hcontrol
  exact Outside.ofFlag_g2_selected_radical_witness S m f X z H h r.refinement r.comparison
    hNT hlinear (h1132 L V D S (.g2 m) f) hcontrol hunique hthree hline hcomponent

/-- Apply the component reduction to the existing marked SL₃/Sp₄ endgame.
The original component equality, surviving list and both radical bounds are
now discharged before that consumer is invoked. -/
theorem ofFlag_source_endgame :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have r := ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115 hcontrol
  obtain ⟨hall, J, hJ⟩ := endgame_of_component_sources S f X z H h r.refinement r.comparison
    hNT hlinear (h1132 L V D S c f) hcontrol h1115 hunique hthree hline hcomponent
  exact ⟨hall, J, hJ, r.radical, r.commutator⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
