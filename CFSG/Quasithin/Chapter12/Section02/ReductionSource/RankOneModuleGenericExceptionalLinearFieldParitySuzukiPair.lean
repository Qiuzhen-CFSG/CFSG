module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSuzukiPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParitySuzuki

/-!
# The actual linear–Suzuki pair for Chapter 12

The proved residual producer supplies maximality and nonfaithfulness on the
original chosen-module setup. The nonsolvable quotient-centralizer branch
then gives the genuine F.1.1 pair, its quasithin generated group, the Suzuki
quotient and the additional F.1.12 Sylow-normality premise. In odd degree,
the already-proved Cartan containment supplies the only extra local hypothesis.
The faithful triple retains the complete overlap of the literal parabolics.

The final two applications deduce the missing Cartan exclusion and odd-degree
kernel solvability from an explicit F.1.12 Suzuki containment theorem. That
independent recognition premise is still unproved; it must be discharged
before the parity owner qt-d-1222-linear-field-parity can complete 5.1.17.

Source: Aschbacher–Smith, 5.1.16–17, pp.639–640, applied in 12.2.2,
p.795; F.1.1 and F.1.9–12, pp.259–264 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual Chapter12 pair satisfies every input to F.1.12, while its
Suzuki factor cannot contain the original Sylow. -/
theorem rankOne_nonsolvable_quotientCentralizer_F112_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hA : A ≤ normalizer (residual H : Set G))
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let R := quotientCentralizerResidual (residual H)
    HypothesisF11 ![L,R] (T : Subgroup G) ∧
      IsQuasithin (generated ![L,R] (T : Subgroup G)) ∧
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal ∧
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
      ¬ (T : Subgroup G) ≤ R := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact quotientCentralizerResidual_F112_inputs hi hH hm hnf hlinear c hA hns

/-- Odd degree discharges the Cartan-normalization premise of the actual
Suzuki pair construction. -/
theorem rankOne_odd_nonsolvable_quotientCentralizer_F112_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let R := quotientCentralizerResidual (residual H)
    HypothesisF11 ![L,R] (T : Subgroup G) ∧
      IsQuasithin (generated ![L,R] (T : Subgroup G)) ∧
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal ∧
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
      ¬ (T : Subgroup G) ≤ R := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact quotientCentralizerResidual_F112_inputs hi hH hm hnf hlinear c
    (cartan_normalizes_residual_of_odd hi hH c hodd hm hnf) hns

/-- F.1.9's faithful local triple for the same odd-degree source pair. -/
theorem rankOne_odd_quotientCentralizer_faithfulTriple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let pair := ![L,quotientCentralizerResidual (residual H)]
    LocallyRankOneTriple
      (fun i => (parabolic pair (T : Subgroup G) i).subgroupOf
        (generated pair (T : Subgroup G)))
      ((commonBorel pair (T : Subgroup G)).subgroupOf (generated pair (T : Subgroup G))) := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact quotientCentralizerResidual_faithfulTriple hi hH hm hnf hlinear c
    (cartan_normalizes_residual_of_odd hi hH c hodd hm hnf) hns

/-- The remaining clause of 5.1.16(2), conditional on the independent
Suzuki containment consequence of F.1.12. -/
theorem rankOne_cartan_not_normalizes_of_suzuki_pair_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    ¬ A ≤ normalizer (residual H : Set G) := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact cartan_not_normalizes_of_suzuki_pair_containment hi hH hm hnf hlinear c hrec hns

/-- On the original odd-degree setup, F.1.12 recognition is the only
remaining input to solvability of the quotient-action kernel. -/
theorem rankOne_odd_quotientCentralizerKernel_solvable_of_suzuki_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R) :
    Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact quotientCentralizerKernel_solvable_of_odd_and_suzuki_containment
    hi hH hm hnf hlinear c hodd hrec

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
