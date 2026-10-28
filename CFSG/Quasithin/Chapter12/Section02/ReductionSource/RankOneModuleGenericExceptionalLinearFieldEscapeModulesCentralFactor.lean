module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCentralFactor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesResidualDisplacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesSuzuki

/-!
# The surviving centralizer factor is a cubic actor

Apply the nonfixed-line argument to the original opposite image and its
intersection with the PSL₃(4) residual centralizer. The earlier exclusion
makes this factor nontrivial. Its cubicity and the whole-action lower bound
force fixed codimension at least twice its rank, including configurations
where the residual intersection also survives.

This supplies cubicity for the remaining factor without a fixed middle
layer. Excluding that factor using the full ambient geometry, and hence
proving the full centralizer span abelian, remain open. The original strict
quadratic-ratio endpoint is unchanged. Final source assembly remains with
qt-d-1222-linear-field-cubic-escape; the earlier local-data choice retains
its separate producer.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open scoped ENNReal
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The surviving factor is a genuine cubic actor, including the mixed case.
The whole-action obstruction forces its fixed codimension to be at least twice its rank. -/
theorem linear_cubic_nonabelian_centralizer_cubic_bound
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
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    let F := E ⊓ centralizer (K : Set (SpanAction.Actor s))
    IsElementaryTwo F ∧ IsCubic (SpanAction.representation s) F ∧
      2 * rank F ≤ fixedCodim (SpanAction.representation s) F := by
  intro S s E K F
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hHT : ¬ H ≤ (T : Subgroup G) :=
    fun hh => hH.1.2 (hh.trans D.sylow_normalizes_component)
  have hc : IsCubic (SpanAction.representation s) F :=
    d.opposite_centralizer_cubic s b hHT g hg hgn
  obtain ⟨he,_⟩ := SpanAction.binary_opposite_image s b g
    (le_conjugateSpanBy C (T : Subgroup G) hg) hgn
  let : IsElementaryAbelian 2 E := he
  have hF : IsElementaryTwo F :=
    ⟨linear_cubic_nonabelian_opposite_centralizer_ne_bot
      D h hH hK hnf hlinear hpsl c d hn hne g hg hgn,
      IsElementaryAbelian.of_le (show F ≤ E from inf_le_left)⟩
  refine ⟨hF,hc,?_⟩
  apply Nat.le_of_not_gt
  intro hsmall
  have hr : actionRatio (SpanAction.representation s) F < 2 := by
    have hz : (rank F : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hF.rank_pos)
    rw [actionRatio,ENNReal.div_lt_iff (Or.inl hz) (Or.inl (by simp))]
    exact_mod_cast hsmall
  exact not_lt_of_ge (linear_cubic_cubicRatio_ge_two D h hH hK hnf hlinear d)
    ((iInf_le_of_le F (iInf_le_of_le ⟨hF,hc⟩ le_rfl)).trans_lt hr)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
