module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesSuzuki
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFixedLine

/-!
# Excluding an abelian two-core quotient in the escaping-cubic branch

A cross-commutator bound into the original four-plane supplies a strict
small cubic actor on the literal centralizer-span action through the
fixed-line hyperplane theorem. The established whole-action lower bound
then gives abelianness of the centralizer span. In particular a contrary
nonabelian span forces [S,S] not to lie in V for its original G.2.3 core.

The cross-commutator bound is explicit. Neither G.2.3's weaker bound into
S₂ nor fixation of a smaller subgroup proves it. The original ambient
exclusion of the remaining nonabelian S/V case remains with this task;
this module does not assert unconditional source 5.1.23.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The literal cross-commutator bound discharges the source cubic obstruction. -/
theorem linear_cubic_abelian_span_of_cross_commutator
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hc : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.W g⁆ ≤ CubicEscape.plane C z) :
    IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))) := by
  by_contra hne
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  have hsmall := SpanAction.binary_opposite_strict_cubic_of_cross_commutator s b g hga hgn hc
    (linear_cubic_nonabelian_rank_gt_one D h hpsl c d hne hn g hg hgn)
  exact not_lt_of_ge (linear_cubic_cubicRatio_ge_two D h hH hK hnf hlinear d) hsmall

/-- Under the original source hypotheses, nonabelianness forces a
nontrivial commutator on the two-core modulo the original plane. -/
theorem linear_cubic_nonabelian_core_commutator
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    ¬ ⁅S.S g,S.S g⁆ ≤ CubicEscape.plane C z := by
  intro S hc
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hindex,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨_,_,_,_,hS,_⟩ :=
    S.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hindex
  have hAS : conjugate (S.W g) g ≤ S.S g := le_sup_right.trans hS.ge
  exact hne (linear_cubic_abelian_span_of_cross_commutator D h hH hK hnf hlinear
    hpsl c d hn g hg hgn ((commutator_mono hAS inf_le_right).trans hc))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
