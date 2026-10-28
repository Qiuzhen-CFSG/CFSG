module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesRankOne


/-!
# The remaining rank-one alternative in the cubic obstruction

The original cubic contributes a noncentral factor inside O₂(L), and the
literal PSL₂ Sylow quotient contributes at least one more. Hence the
opposite image in the original faithful projection has positive rank.
The previously proved higher-field bound and Cartan parity leave either
rank greater than one or field degree two and rank one. In the latter
case the same opposite image is a quadratic offender with fixed
codimension at most two on the centralizer-span action.

These are applications of the G.2.3 span construction to the original
Cartan and local data, without selecting another constituent. Excluding
the field-four alternative and proving middle-layer fixedness remain
obligations of the abelian-span argument; no abelian-span result is asserted.

Source: Aschbacher--Smith 5.1.21--23, printed pp.644--646,
refs/quasithin.pdf. Final field-four/Borel assembly is owned by
qt-d-1222-linear-field-four-borel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- One cubic factor in O₂(L) and one in the original PSL₂ Sylow quotient. -/
theorem linear_cubic_sylow_length_ge_two
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n) :
    2 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L) := by
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
  have hlog : 1 ≤ Nat.log 4 (2 ^ n) := Nat.le_log_of_pow_le (by decide)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn)
  omega

/-- The opposite image in the original faithful projection is nontrivial. -/
theorem linear_cubic_nonabelian_rank_pos
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    0 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  have hlower := linear_cubic_sylow_length_ge_two D h hpsl c d hn
  rw [linear_cubic_nonabelian_sylow_length D h hpsl c d hne g hg hgn] at hlower
  dsimp only at hlower ⊢
  omega

/-- The rank-one alternative is a quadratic offender for the literal span action. -/
theorem linear_cubic_nonabelian_rank_one_offender
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hrank : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      rank (((conjugate (S.W g) g).subgroupOf S.H).map
        (SpanAction.projection (linear_cubic_centralizer_setup h d))) = 1) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    IsElementaryTwo E ∧ IsQuadratic (SpanAction.representation s) E ∧
      fixedCodim (SpanAction.representation s) E ≤ 2 ∧
      quadraticRatio (SpanAction.representation s) ≤ 2 := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨he,hq,hc⟩ := SpanAction.binary_opposite_rank_one_offender s b g hga hgn hrank
  exact ⟨he,hq,hc,
    SpanAction.binary_opposite_quadraticRatio_le_two_of_rank_one s b g hga hgn hrank⟩

/-- Outside the proved strict-rank branch, the field is four and the same
opposite subgroup gives a concrete quadratic bound. Excluding this alternative
still requires the component argument; no middle-layer fixedness is assumed. -/
theorem linear_cubic_nonabelian_rank_gt_one_or_field_four_offender
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    1 < rank E ∨ (n = 2 ∧ rank E = 1 ∧
      IsElementaryTwo E ∧ IsQuadratic (SpanAction.representation s) E ∧
      fixedCodim (SpanAction.representation s) E ≤ 2 ∧
      quadraticRatio (SpanAction.representation s) ≤ 2) := by
  let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
  let s := linear_cubic_centralizer_setup h d
  let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
  change 1 < rank E ∨ (n = 2 ∧ rank E = 1 ∧ _)
  by_cases hm : 1 < rank E
  · exact Or.inl hm
  have hp : 0 < rank E := linear_cubic_nonabelian_rank_pos D h hpsl c d hne hn g hg hgn
  have he : n = 2 ∨ 1 < rank E :=
    linear_cubic_nonabelian_rank_gt_one_or_field_four D h hpsl c d hne hn g hg hgn
  have h1 : rank E = 1 := by omega
  exact Or.inr ⟨he.resolve_right hm,h1,
    linear_cubic_nonabelian_rank_one_offender D h hpsl c d hne g hg hgn h1⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
