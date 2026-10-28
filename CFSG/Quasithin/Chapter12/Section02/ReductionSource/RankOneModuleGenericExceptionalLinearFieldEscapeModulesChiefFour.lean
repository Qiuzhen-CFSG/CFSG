module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefFour

/-!
# Closing the field-four rank-one branch on the original span

The original plane's L-span forces two cubic factors in O₂(L); the
PSL₂(4) Sylow quotient contributes a third. The previously proved exact
chief-count identity therefore excludes rank one on the same faithful
opposite projection. Combining this with the higher-field result gives
rank greater than one whenever n>1.

The final consumer applies D.2.13 with this rank premise discharged.
Middle-layer fixedness remains explicit and must still be proved before
the abelian-span and constituent argument can be completed.
Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Two cubic factors in O₂(L) and a third on its original Sylow quotient. -/
theorem linear_cubic_sylow_length_ge_three_of_field_four
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2))
    (c : LinearFieldCartan T L H A B C 2)
    (d : CubicEscape.LocalData T H C z) :
    3 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) := by
  have hchar : L ⊔ (T : Subgroup G) ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    refine ⟨?_,fun x hx => mem_sup_right hx⟩
    intro he
    exact D.ne_bot (bot_unique (D.le_core.trans he.le))
  have hc := d.core_cubic_length_ge_two_of_field_four hpsl c.cubic_card
    (c.cubic_le.trans (c.left_le.trans inf_le_left))
    D.sylow_normalizes_component
    (c.cubic_le.trans (c.left_le.trans inf_le_right)) (Chapter1.mem_He_iff.mp hchar)
  rw [psl_cubic_sylow_length hpsl D.sylow_normalizes_component c.cubic_card
    (c.cubic_le.trans (c.left_le.trans inf_le_left))
    (c.cubic_le.trans (c.left_le.trans inf_le_right))]
  change 3 ≤ conjugationCubicLength C (L.pCoreIn 2) + 1
  omega

/-- Field four also has strict rank growth on the literal opposite image. -/
theorem linear_cubic_nonabelian_rank_gt_one_of_field_four
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2))
    (c : LinearFieldCartan T L H A B C 2)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  have hlower := linear_cubic_sylow_length_ge_three_of_field_four D h hpsl c d
  rw [linear_cubic_nonabelian_sylow_length D h hpsl c d hne g hg hgn] at hlower
  dsimp only at hlower ⊢
  omega

/-- The original opposite actor has rank greater than one for every n>1. -/
theorem linear_cubic_nonabelian_rank_gt_one
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  rcases linear_cubic_nonabelian_rank_gt_one_or_field_four D h hpsl c d hne hn g hg hgn with he | he
  · subst n
    exact linear_cubic_nonabelian_rank_gt_one_of_field_four D h hpsl c d hne g hg hgn
  · exact he

/-- The literal cubic bound now requires only the missing middle-layer fixedness. -/
theorem linear_cubic_strict_cubic_of_middle_fixed
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
    cubicRatio (SpanAction.representation (linear_cubic_centralizer_setup h d)) < 2 := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  exact SpanAction.binary_opposite_strict_cubic_of_middle_fixed s b g hga hgn hfix
    (linear_cubic_nonabelian_rank_gt_one D h hpsl c d hne hn g hg hgn)

/-- The chief count discharges the rank premise of the actual D.2.13 application. -/
theorem linear_cubic_fitting_of_middle_fixed
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
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
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
  exact linear_cubic_fitting_of_opposite_geometry D h hH hK hnf hlinear hpsl c d hne
    g hg hgn hfix (linear_cubic_nonabelian_rank_gt_one D h hpsl c d hne hn g hg hgn)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
