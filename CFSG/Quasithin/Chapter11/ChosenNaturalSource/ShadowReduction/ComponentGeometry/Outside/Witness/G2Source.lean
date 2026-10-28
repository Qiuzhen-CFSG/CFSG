module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison.Source

/-!
# The original G₂ radical witness with source weak closure discharged

The completed original 11.2.2 parameter theorem gives s(G,V)=2n>1.
The full-center G₂ source theorem supplies both closure bounds on the
literal R₁. Substituting these proved bounds into the existing witness
construction retains H₁=R₁O²(H), its actual Sylow subgroup and both
generation-one conclusions. Its application to the completed rank-one
consumer proves the original G₂ contradiction in 11.5.1.

Only independently owned preceding source inputs remain: maximal-local
uniqueness, the third-space centralizer, the fixed line and second-component
uniqueness, earlier component geometry, the surviving list, full 11.3.2,
Kz=K and the Sylow normalizer bound. Their final discharge belongs to
qt-d-1222-shadow-components and its earlier-source producers. The exact
OddKernelNormalizer remains with qt-d-1222-natural-odd-kernel-normalizer.
No G₂ weak-closure or R₁-Sylow equality is assumed here. This does not
complete universal generation one in the remaining field-four markings.
Source: Aschbacher–Smith 11.2.2(3,5–6), 11.4.3–4 and 11.5.1,
printed pp.767–768,778–779 of refs/quasithin.pdf.
-/

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
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (LocalGeometry.sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include h hcase he hNT hlinear h1132 hcontrol hunique hthree hline hcomponent in
/-- Construct the original selected H and its R₁O²(H) witness from the
preceding source geometry, with the G₂ closure assumptions discharged. -/
theorem ofFlag_g2_selected_radical_witness :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype := by
  have hp := LocalGeometry.WeakClosure.Parameters.source_parameters D S f hunique hthree hline
  have hs : (1 : ℕ∞) < @globalS G _ V D.elementary := by
    rw [hp.2.2.1.2]
    change (1 : ℕ∞) < ((2 * S.field.degree : ℕ) : ℕ∞)
    exact_mod_cast (show 1 < 2 * S.field.degree by have := S.nonbinary; omega)
  obtain ⟨_,_,_,hC,_,hN⟩ :=
    LocalGeometry.WeakClosure.G2.CenterComparison.source_clauses D S m f
      hunique hthree hline hcomponent
  exact ofFlag_surviving_selected_radical_witness S f X z H h hcase he hNT
    hlinear h1132 hcontrol hs hC hN

include h hcase he hNT hlinear h1132 hcontrol hunique hthree hline hcomponent in
/-- Source 11.5.1 on the original G₂ marking: the constructed witness
feeds the literal rank-one consumer with all closure bounds proved. -/
theorem ofFlag_g2_impossible_from_preceding : False := by
  obtain ⟨J,_,_,_,_,w,_⟩ := ofFlag_g2_selected_radical_witness S m f X z H
    h hcase he hNT hlinear h1132 hcontrol hunique hthree hline hcomponent
  exact LocalGeometry.WeakClosure.G2.CenterComparison.rankOne_impossible D S m f
    hunique hthree hline hcomponent w.H₁ w.sylow w.sylow_image
    w.generation_one w.outside

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
