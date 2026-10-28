module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChief
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane

/-!
# Closing the higher-field chief-count branch of the cubic obstruction

The chosen module makes O₂(LT) nontrivial; condition (E) gives its
self-centralizing property. The original four-plane then contributes
at least one cubic factor in O₂(L), while the literal PSL₂ Sylow quotient
adds log₄(2ⁿ). For n≥4 this proves the three-factor bound, hence rank(A*)>1
for the previously constructed projection. Cartan parity leaves only n=2.

The final theorem applies this bound to the existing D.2.13 consumer.
Middle-layer fixedness, the field-four count and the constituent argument
remain obligations of this task; no abelian-span conclusion is asserted.
Source: Aschbacher--Smith 5.1.21--23, printed pp.644--646,
refs/quasithin.pdf. Final field-four/Borel assembly is owned by
qt-d-1222-linear-field-four-borel (which absorbed the earlier escape assembly).
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- One factor in O₂(L) and at least two above it, on the original Sylow. -/
theorem linear_cubic_sylow_length_ge_three_of_large_field
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 4 ≤ n) :
    3 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) := by
  have hchar : L ⊔ (T : Subgroup G) ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    refine ⟨?_,fun x hx => mem_sup_right hx⟩
    intro he
    exact D.ne_bot (bot_unique (D.le_core.trans he.le))
  have hc := d.core_cubic_length_pos c.cubic_card
    (c.cubic_le.trans (c.left_le.trans inf_le_left))
    D.sylow_normalizes_component (Chapter1.mem_He_iff.mp hchar)
  rw [psl_cubic_sylow_length hpsl D.sylow_normalizes_component c.cubic_card
    (c.cubic_le.trans (c.left_le.trans inf_le_left))
    (c.cubic_le.trans (c.left_le.trans inf_le_right))]
  have hlog : 2 ≤ Nat.log 4 (2 ^ n) := Nat.le_log_of_pow_le (by decide)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn)
  omega

/-- The same faithful opposite projection has rank greater than one. -/
theorem linear_cubic_nonabelian_rank_gt_one_of_large_field
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 4 ≤ n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  have hlower := linear_cubic_sylow_length_ge_three_of_large_field D h hpsl c d hn
  rw [linear_cubic_nonabelian_sylow_length D h hpsl c d hne g hg hgn] at hlower
  dsimp only at hlower ⊢
  omega


/-- The Cartan forces even field degree. The rank obstruction is therefore
settled outside the remaining field-four case, without a natural-module premise. -/
theorem linear_cubic_nonabelian_rank_gt_one_or_field_four
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    n = 2 ∨ 1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  by_cases he : n = 2
  · exact Or.inl he
  have hdiv : 3 ∣ 2 ^ n - 1 := by
    rw [← c.cubic_card, ← c.left_card]
    exact card_dvd_of_le c.cubic_le
  obtain ⟨k,hk⟩ := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hdiv
  exact Or.inr (linear_cubic_nonabelian_rank_gt_one_of_large_field D h hpsl c d hne
    (by omega) g hg hgn)

/-- The proved rank bound discharges the chief-count premise in D.2.13.
Middle-layer fixedness is still an explicit obligation of this task. -/
theorem linear_cubic_fitting_of_large_field
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
    (hn : 4 ≤ n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let C₁ := ((linearResidualAction H).comp i).ker
    let N₁ := C₁.map (SpanAction.projection s)
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧
      E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      (fittingSubgroup N₁).map N₁.subtype ≤ centralizer (E : Set (SpanAction.Actor s)) := by
  exact linear_cubic_fitting_of_opposite_geometry D h hH hK hnf hlinear hpsl c d hne
    g hg hgn hfix
    (linear_cubic_nonabelian_rank_gt_one_of_large_field D h hpsl c d hne
      hn g hg hgn)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
