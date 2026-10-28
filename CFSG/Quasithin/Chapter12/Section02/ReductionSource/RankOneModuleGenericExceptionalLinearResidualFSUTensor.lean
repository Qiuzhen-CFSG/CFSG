module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualFSUTensor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidual

/-!
# The tensor-row obstruction on the Chapter 12 residual

The actual chosen-module normalization and H* membership force a diagram
actor on the embedded residual. Hence no Fundamental Setup on that residual
can have the literal Hermitian tensor marking. Conditional recognition of
this marking gives nonfaithfulness, and the existing geometry then gives
centralization and exact maximal-overgroup uniqueness.

These applications retain maximality and module recognition explicitly.
They do not prove unconditional 5.1.14. The remaining J₄ exclusion and FSU
classification stay with qt-d-1222-linear-residual-maximal-nonfaithful;
qt-d-1222-rankone-exceptional-linear-analysis retains final source assembly.
Source: Aschbacher–Smith 3.2.9(4), pp.582–583, and 5.1.14, pp.638–639,
as used in 12.2.2 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The tensor row is excluded on every actual residual FSU. -/
theorem rankOne_linear_residual_fsu_not_hermitian
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T (residual H)) :
    ¬ Nonempty F.HermitianFourMarking :=
  linear_residual_fsu_not_hermitian D.sylow_normalizes_component hH hlinear F

/-- Recognition of the original FSU module discharges nonfaithfulness after
the separate maximality assertion has been proved. -/
theorem rankOne_linear_residual_nonfaithful_of_hermitian_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : ∀ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), Nonempty F.HermitianFourMarking) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) :=
  linear_residual_nonfaithful_of_hermitian_recognition h.simpleQTKE
    D.sylow_normalizes_component hH hlinear hmax hmodel

/-- Literal application to the existing residual geometry, retaining the two
remaining mathematical obligations of this task. -/
theorem rankOne_linear_residual_geometry_of_hermitian_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : ∀ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), Nonempty F.HermitianFourMarking) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) := by
  exact residual_geometry_of_maximal_nonfaithful h.simpleQTKE hH.1.1 hmax
    (D.rankOne_linear_residual_nonfaithful_of_hermitian_recognition
      h hH hlinear hmax hmodel)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
