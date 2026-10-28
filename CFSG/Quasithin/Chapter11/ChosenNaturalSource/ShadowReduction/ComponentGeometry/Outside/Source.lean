module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.OddBlock
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.G2Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source

/-!
# The outside source conclusions with odd-kernel control discharged

Apply the completed nonbinary specialization of 4.4.3 and Remark 4.4.2
to the original chosen module. This removes the Hall-faithfulness premise
in the universal generation-one theorem, including the full SL₃(4) cover.
Together with the actual quotient-centralizer products this gives all clauses
of 11.4.3–4 and the choice of H with its literal O²(H) alternative.

For the original G₂ marking, the preceding weak-closure results construct
H₁ = R₁O²(H), its inclusion in H, escape from M and actual R₁-Sylow image.
The resulting subgroup feeds the original E.3.19 contradiction in 11.5.1.
The field flag, full covering kernels and relative normality are unchanged.

Earlier geometry, the surviving refinement, Kz=K, full Proposition1132At
and the preceding 11.1.5 alternative remain inputs from the component,
triangle, linear-geometry and local-geometry producers. Their final discharge
belongs to qt-d-1222-shadow-components. No native-cover or odd-kernel premise
remains in these applications.

Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.778–779,
11.4.3–4 and 11.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- All clauses of original 11.4.3–4 and the source choice of H, with the
normalizer theorem applied to the same chosen module and full quotient. -/
theorem ofFlag_source_products_and_generation
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    let E := ofFlag S f X z H
    (∀ g ∈ Gz E, ∃ k ∈ E.K, ∃ y ∈ Yz E, ∃ m ∈ Mz E, g = k * y * m) ∧
    (E.K = E.L₁ → ¬ Yz E ≤ E.M) ∧
    (∀ g ∈ E.G₁, ∃ k ∈ E.K, ∃ y ∈ E.Y, ∃ m ∈ E.M₁, g = k * y * m) ∧
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) E.M →
      J ≤ Gz E → ChapterE.generationParameter J = 1) ∧
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) E.M ∧
      J ≤ Gz E ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  obtain ⟨hp, hl⟩ := Models.ofFlag_surviving_products S f X z H
    h hcase he hNT hlinear h1132
  have hout := kernel_outside_of_equal (ofFlag S f X z H) h he hNT
    (Models.ofFlag_surviving_outer_twoClosed S f X z H h hcase) h1132
  obtain ⟨hall, hselected⟩ := Generation.ofFlag_selected_and_universal_generation_one
    S f X z H h hcase he hNT hlinear h1132
    (LocalGeometry.WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S)
    h1115
  exact ⟨hp, hout, hl, hall, hselected⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (.g2 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (LocalGeometry.sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include h hcase he hNT hlinear h1132 hunique hthree hline hcomponent

/-- The actual source R₁-Sylow witness, with both its weak-closure and
odd-kernel premises proved. The earlier component geometry remains explicit. -/
theorem ofFlag_g2_source_radical_witness :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype := by
  exact ofFlag_g2_selected_radical_witness S m f X z H h hcase he hNT hlinear h1132
    (LocalGeometry.WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_unconditional D S)
    hunique hthree hline hcomponent

/-- Apply the constructed subgroup, its literal Sylow image and generation
one to E.3.19, giving original 11.5.1 on the G₂ marking. -/
theorem ofFlag_g2_source_impossible : False := by
  obtain ⟨J, _, _, _, _, w, _⟩ := ofFlag_g2_source_radical_witness S m f X z H
    h hcase he hNT hlinear h1132 hunique hthree hline hcomponent
  exact LocalGeometry.WeakClosure.G2.CenterComparison.rankOne_impossible D S m f
    hunique hthree hline hcomponent w.H₁ w.sylow w.sylow_image
    w.generation_one w.outside

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
