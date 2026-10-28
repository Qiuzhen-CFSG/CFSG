module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupFullFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityBlockExclusion

/-!
# Original field parity conditional only on Suzuki containment

Apply full residual-normalizer fusion to the literal ChosenModule point
in every odd degree. The existing consumer then proves global TI, excludes
the block, proves the required abelianness, constructs every F.8 and Seed
clause, and applies the degree-three displacement and both terminal branches.
No residual TI, normality, marking, block or Seed callback remains.

Evenness is proved first under solvability of the actual quotient-action
kernel and then under the exact independent F.1.12 Suzuki containment
premise. The source theorem is still conditional until
qt-f112-linear-suzuki-containment proves that premise; final assembly
remains with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith 5.1.17, printed pp.640–642, used in 12.2.2,
printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Chapter6.Source.RankOneGeneric LinearParity ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The literal chosen point has TI under the whole residual normalizer. -/
theorem rankOne_odd_point_ti_under_residual_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    {g : G} (hg : g ∈ normalizer (residual H : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ V
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_point_ti_under_residual_normalizer hi hH hm hnf hlinear hsolv F c hodd hnat hg

/-- All geometric and module premises of the original parity argument are discharged;
only solvability of the actual quotient-action kernel remains. -/
theorem rankOne_even_exponent_of_quotientCentralizerKernel_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) : Even n := by
  apply D.rankOne_even_exponent_of_solvable_and_residual_ti h hmany hn hpsl hH hlinear hgen hsolv
  intro A B c ho g hg
  exact D.rankOne_odd_point_ti_under_residual_normalizer h hmany hn hpsl hH hlinear c ho hsolv hg

/-- Final conditional assembly retains exactly the independent F.1.12 recognition
input; full residual/global TI, F.8, Seed, and both terminal branches are proved. -/
theorem rankOne_even_exponent_of_suzuki_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgen : 1 < ChapterE.generationParameter H)
    (hrec : ∀ R : Subgroup G,
      HypothesisF11 ![L,R] (T : Subgroup G) →
      IsQuasithin (generated ![L,R] (T : Subgroup G)) →
      ((T : Subgroup G).subgroupOf
        ((T : Subgroup G) ⊔ borel R (T : Subgroup G))).Normal →
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ≤ R) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
  have hs := D.rankOne_odd_quotientCentralizerKernel_solvable_of_suzuki_containment
    h hmany hn hpsl hH hlinear c ho hrec
  exact D.rankOne_even_exponent_of_quotientCentralizerKernel_solvable h hmany hn hpsl hH hlinear hgen hs
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
