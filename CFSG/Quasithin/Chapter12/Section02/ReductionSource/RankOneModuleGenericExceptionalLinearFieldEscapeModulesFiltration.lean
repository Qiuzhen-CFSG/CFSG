module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesBinary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration

/-!
# The literal middle-layer budget and D.2.13 application

The original Cartan and LocalData construct the G.2.3 natural data and a
moving element of the actual cubic. On the faithful centralizer-span
quotient, its opposite image has the proved middle-layer codimension and
third-displacement containment.

The second theorem feeds the concrete fixed-layer and rank hypotheses
into the strict cubic bound and the existing minimum-offender Fitting
centralization theorem. These geometric hypotheses still belong to this
source-theorem owner; neither the abelian span nor the component/diagram
contradiction is asserted here. Final classification assembly remains
qt-d-1222-linear-field-cubic-escape.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

theorem linear_cubic_nonabelian_middle_codimension
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    ∃ g ∈ C, g ∉ normalizer (zpowers z : Set G) ∧
      let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
      Module.finrank (ZMod 2) ((SpanAction.conjugationSection s).imageSpace (S.S₂ g)) +
        (rank E + 1) = Module.finrank (ZMod 2) (Additive (SpanAction.moduleSubgroup s)) ∧
      (∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ v : Additive (SpanAction.moduleSubgroup s),
        displacement (SpanAction.representation s) a (displacement (SpanAction.representation s) b
          (displacement (SpanAction.representation s) c v)) ∈
            (SpanAction.conjugationSection s).imageSpace S.V) ∧
      (∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E,
        ∀ v : Additive (SpanAction.moduleSubgroup s),
        displacement (SpanAction.representation s) a (displacement (SpanAction.representation s) b
          (displacement (SpanAction.representation s) c
            (displacement (SpanAction.representation s) e v))) = 0) := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  exact ⟨g,hg,hgn,SpanAction.binary_opposite_middle_codimension s b g hga hgn,
    SpanAction.binary_opposite_third_displacement s b g hga hgn,
    SpanAction.binary_opposite_fourth_displacement s b g hga hgn⟩

theorem linear_cubic_fitting_of_opposite_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z)
    (hm : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
        (SpanAction.projection (linear_cubic_centralizer_setup h d)))) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let C₁ := ((linearResidualAction H).comp i).ker
    let N := C₁.map (SpanAction.projection s)
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧
      E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      (fittingSubgroup N).map N.subtype ≤ centralizer (E : Set (SpanAction.Actor s)) := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  exact linear_cubic_minimum_fitting_centralization h hH hK hnf hlinear d
    (SpanAction.binary_opposite_strict_cubic_of_middle_fixed s b g hga hgn hfix hm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
