module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Source

/-!
# Component reduction with odd-kernel control discharged in the marked rows

The only unresolved odd-kernel row is the full SL₃(4) central cover. The
proved normalizer theorems exclude it for every larger field and for the
actual Sp₄ and G₂ quotient markings. Applying them to the original chosen
module discharges the normalizer input in 11.4.1–4. In the G₂ branch the
same marking supplies the selected H and its literal R₁O²(H) subgroup,
with escape, generation one and an actual R₁-Sylow witness.

All preceding flag geometry and the full Proposition1132At implication
remain explicit, with final discharge by qt-d-1222-natural-shadow-reduction.
The general field-four SL₃ normalizer input retains its existing producer
qt-d-1222-natural-odd-kernel-normalizer through the outside-witness owner
qt-d-1222-shadow-component-witness. These applications do not discharge it.
The terminal E.3.19 contradiction remains with the shadow assembly owner.

Source: Aschbacher–Smith, refs/quasithin.pdf, 11.4.1–4 and 11.5.1,
printed pp.775–779; the normalizer step is 4.4.3 and Remark 4.4.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

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

/-- The complete original component reduction for every field larger than four,
with the earlier odd-kernel normalizer premise proved. -/
theorem ofFlag_source_reduction_of_field_ne_four (hf : S.field.degree ≠ 2) :
    SourceReductionAt (ofFlag S f X z H) := by
  exact ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_field_ne_four D S hf)

/-- The complete component reduction on an actual symplectic quotient marking,
including the field-four case and generation one for every outside H. -/
theorem ofFlag_source_reduction_of_sp4
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S.field)) :
    SourceReductionAt (ofFlag S f X z H) := by
  exact ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_sp4 D S m.groupEquiv)

/-- The complete component reduction on an actual G₂ quotient marking.
No odd-kernel control is assumed, including when the field has order four. -/
theorem ofFlag_source_reduction_of_g2
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S.field)) :
    SourceReductionAt (ofFlag S f X z H) := by
  exact ofFlag_source_reduction S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_g2 D S m.groupEquiv)

variable
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))

include hunique hthree hline hcomponent

/-- Construct the source-selected H and its outside R₁O²(H) subgroup on the
original G₂ flag. Its Sylow image and both generation-one conclusions are
proved, with only the registered preceding geometry and full 11.3.2 retained. -/
theorem ofFlag_g2_source_witness_of_preceding
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S.field))
    (hm : c = .g2 m) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 ∧
      ∃ w : OutsideRadicalWitness (ofFlag S f X z J),
        w.H₁ = (ofFlag S f X z J).R₁ ⊔ (pResidual 2 J).map J.subtype := by
  exact ofFlag_g2_source_witness S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_g2 D S m.groupEquiv)
    hunique hthree hline hcomponent m hm

/-- The surviving endgame on an actual symplectic marking, including q=4.
The same selected H carries its O²(H) alternative, both products and the
radical bounds, without an odd-kernel normalizer callback. -/
theorem ofFlag_source_endgame_of_sp4
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S.field)) :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact ofFlag_source_endgame S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_sp4 D S m.groupEquiv) hunique hthree hline hcomponent

/-- The same surviving endgame for every original field larger than four,
including the linear-three marking. The full field-four linear row remains
with the independent odd-kernel normalizer producer. -/
theorem ofFlag_source_endgame_of_field_ne_four (hf : S.field.degree ≠ 2) :
    (∀ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      J ≤ centralizer ({z} : Set G) → ChapterE.generationParameter J = 1) ∧
    ∃ J, EndgameAt (ofFlag S f X z J) ∧
      (ofFlag S f X z J).R₁ ≤
        (solvableRadical ((ofFlag S f X z J).K ⊔ (T : Subgroup G) : Subgroup G)).map
          ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).subtype ∧
      ⁅(ofFlag S f X z J).R₁, X⁆ ≤
        ((ofFlag S f X z J).K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact ofFlag_source_endgame S f X z H h hNT hlinear hcent hcartan_line
    hX hXR hKZ h701 h1132 h1122 href h1115
    (WeakClosure.Generation.OddNormalizer.oddKernelNormalizer_of_field_ne_four D S hf) hunique hthree hline hcomponent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
