module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergFullStar
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialExclusion
public import Theory.GroupTheory.HeisenbergResidualComparison

/-!
# Comparing the proper local and full residuals under solvability

The original proper local supplies a normal Heisenberg image R in H/O₂(H)
with centralizer exactly L₁*, the center of R. The actual outer action
therefore has kernel R. The full two-residual contains R, and its quotient
by R is trivial, cubic, or isomorphic to the literal SL₂(3) model.

The established extraspecial exclusion applies to the equality branch
through the literal equality with the full residual. Consequently the
local image is proper in that residual, with cubic or SL₂(3) quotient.
The SL₂(3) branch is retained without assuming a splitting; both nontrivial
branches remain to be excluded by the subsequent source argument.

Source: Aschbacher–Smith 14.7.15(3), 14.7.27–29, printed
pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original solvability hypothesis constructs the proper local and
compares its actual image with the full residual, retaining every branch. -/
theorem original_solvable_full_residual_comparison
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      ∃ hRn : R.Normal, letI := hRn
        Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) ∧
        (R = pResidual 2 (HStar F.H) ∨
          Nat.card ((pResidual 2 (HStar F.H)) ⧸
            R.subgroupOf (pResidual 2 (HStar F.H))) = 3 ∨
          Nonempty (((pResidual 2 (HStar F.H)) ⧸
            R.subgroupOf (pResidual 2 (HStar F.H))) ≃*
              Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) := by
  obtain ⟨I,hIH,hI,hRn,he,hR3,hRres,hZ,hC⟩ :=
    original_solvable_full_star_centralizer d h hab structural previous faithful earlier hs
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hCR : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  exact ⟨I,hIH,hI,hRn,he,hR3,hRres,hZ,hC,
    heisenberg_twoResidual_comparison R he.some hCR hRres⟩

/-- Applying the full-residual exclusion only after identifying its literal
equality branch leaves a proper local image and the two nontrivial quotients. -/
theorem original_solvable_full_residual_strict
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      ∃ hRn : R.Normal, letI := hRn
        Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R < pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) ∧
        (Nat.card ((pResidual 2 (HStar F.H)) ⧸
            R.subgroupOf (pResidual 2 (HStar F.H))) = 3 ∨
          Nonempty (((pResidual 2 (HStar F.H)) ⧸
            R.subgroupOf (pResidual 2 (HStar F.H))) ≃*
              Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) := by
  obtain ⟨I,hIH,hI,hRn,he,hR3,hRres,hZ,hC,hcomp⟩ :=
    original_solvable_full_residual_comparison d h hab structural previous faithful earlier hs
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  change Nonempty (R ≃* HeisenbergPrime 3) at he
  have hne : R ≠ pResidual 2 (HStar F.H) := by
    intro heq
    apply extraspecial_star_residual_impossible d h hab structural previous faithful earlier
    exact ⟨(MulEquiv.subgroupCongr heq).symm.trans he.some⟩
  exact ⟨I,hIH,hI,hRn,he,hR3,lt_of_le_of_ne hRres hne,hZ,hC,
    hcomp.resolve_left hne⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
