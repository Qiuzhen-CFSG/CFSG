module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSuzuki
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityKernelFusion

/-!
# The actual nonsolvable quotient-centralizer branch in Chapter 12

The proved residual producer supplies maximality in the original local
family. The Chapter6 source argument then identifies C_K^∞/O₂ with a
Suzuki matrix group, proves its exact ambient normalizer N_G(K), and
excludes C_K^∞ from N_G(L). The intrinsic residual is also the unique
C-component of the literal quotient-centralizer C_K.

These are the first two assertions of original 5.1.16(2). The Cartan
exclusion, resulting kernel solvability, residual-normalizer TI and block
exclusion remain with the final owner qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.16(2), pp.639–640, applied in 12.2.2,
p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The nonsolvable branch on the literal Chapter12 residual, with its actual
matrix quotient, relative component, normalizer and escape conclusion. -/
theorem rankOne_nonsolvable_quotientCentralizer_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hns : ¬ Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    (solvableResidual (quotientCentralizer (residual H))).IsCComponent ∧
    (∀ J : Subgroup (quotientCentralizer (residual H)), J.IsCComponent →
      J = solvableResidual (quotientCentralizer (residual H))) ∧
    normalizer (quotientCentralizerResidual (residual H) : Set G) =
      normalizer (residual H : Set G) ∧
    ¬ quotientCentralizerResidual (residual H) ≤ normalizer (L : Set G) ∧
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty
      ((quotientCentralizerResidual (residual H) ⧸
        pCore 2 (quotientCentralizerResidual (residual H))) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  obtain ⟨hm,_⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  have hg := nonsolvable_quotientCentralizer_geometry hi hH hm hlinear hns
  have hTN : (T : Subgroup G) ≤ normalizer (residual H : Set G) :=
    hH.1.1.2.trans (le_normalizer_residual H)
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hi.qtke T hm).normalizer_maximal
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hc := nonsolvable_quotientCentralizer_residual_suzuki (residual H)
    (hi.qtke.twoLocal_sqtk hmax.1) (linear_residual_quotient hlinear) hns
  exact ⟨hc.1,hc.2.1,hg⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
