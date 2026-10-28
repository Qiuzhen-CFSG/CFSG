module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParitySolvableCore

/-!
# Quotient-centralizer TI on the chosen Chapter12 module

The actual residual producer supplies maximality and nonfaithfulness.
These discharge Baumann control in this branch, without an additional
uniqueness or Baumann premise. The chosen natural marking then gives
TI for Ω₁Z(T) ∩ V under the literal quotient-action kernel joined with T.

Kernel solvability is still the original 5.1.16(2) obligation. Its proof,
the extension of TI to the full residual normalizer, and block exclusion
remain with the final parity owner qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.17, p.640, applied in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The original linear-residual branch discharges Baumann control. -/
theorem rankOne_baumann_normalizer_le_of_linear_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact baumann_normalizer_le_of_nonfaithful_residual hi hH hm hnf

/-- Point TI under the actual solvable quotient-centralizer and Sylow join. -/
theorem rankOne_odd_point_ti_under_solvable_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    {g : G} (hg : g ∈
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ (T : Subgroup G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ V
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_point_ti_under_solvable_kernel hi hH hm hnf hlinear hsolv F hodd hnat hg
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
