module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Action
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix

/-!
# The intrinsic core and cubic quotient of the concrete J₄ centralizer

The certified self-centralizing two-core of C_Model(a) is its generalized
Fitting subgroup. Transport the actual quotient action along this equality,
then compose with conjugation on the native Mathieu group. The scalar-kernel
theorem proves that this surjection retains exactly three elements in its
kernel. The projection formula records the original centralizer quotient map.

These are the local structural clauses in Aschbacher–Segev's definition of
type J₄, *The study of J₄ via the theory of uniqueness systems* (1992), p.12,
used in Aschbacher–Smith 8.2.14, printed p.723. The separate `Fusion` module
supplies the returning ambient conjugate required by that definition.
-/

public section

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

namespace Theory.GroupTheory.Recognition.JankoFour
namespace ModelHypotheses
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- Self-centralization identifies the intrinsic generalized Fitting subgroup. -/
theorem core_eq_twoCore : core Janko4.a = pCore 2 (centralizer Janko4.a) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (@Theory.Quasithin.centralizer_pCore_le_iff
    Janko4.InvolutionCentralizers.First.centralizer involutionCentralizer
    inferInstance inferInstance 2
    Janko4.InvolutionCentralizers.First.centralizerEquiv).mpr
      localTwoCoreCentralizerControl.1

/-- The exact quotient by F*(C), identified through the certified core action. -/
noncomputable def coreQuotientEquiv :
    ((centralizer Janko4.a) ⧸ core Janko4.a) ≃* TwoCoreLinearModel.actionGroup :=
  (QuotientGroup.quotientMulEquivOfEq core_eq_twoCore).trans
    Janko4.InvolutionCentralizers.First.quotientEquiv

/-- The quotient equivalence retains the actual conjugation action. -/
theorem coreQuotientEquiv_mk (c : centralizer Janko4.a) :
    (coreQuotientEquiv (QuotientGroup.mk' (core Janko4.a) c) :
      TwoCoreLinearModel.Matrix12ˣ) =
        Janko4.InvolutionCentralizers.First.quotientAction
          (Janko4.InvolutionCentralizers.First.centralizerEquiv c) := by
  exact Janko4.InvolutionCentralizers.First.quotientEquiv_mk c

/-- The full quotient surjects onto Aut(M₂₂) with a three-element kernel. -/
noncomputable def cubicQuotient :
    CubicAutomorphismQuotient ((centralizer Janko4.a) ⧸ core Janko4.a) where
  projection := Janko4.InvolutionCentralizers.First.QuotientExtension.quotientConjugation.comp
    coreQuotientEquiv.toMonoidHom
  surjective :=
    Janko4.InvolutionCentralizers.First.QuotientExtension.quotientConjugation_surjective.comp
      coreQuotientEquiv.surjective
  kernel_card := by
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_comp_mulEquiv,
      Janko4.InvolutionCentralizers.First.QuotientExtension.quotientConjugation_ker]
    exact (Nat.card_congr (coreQuotientEquiv.symm.subgroupMap
      Janko4.InvolutionCentralizers.First.QuotientExtension.scalarSubgroup).toEquiv).symm.trans
        Janko4.InvolutionCentralizers.First.QuotientExtension.scalarSubgroup_card

/-- The cubic projection respects the literal centralizer quotient maps. -/
theorem cubicQuotient_projection_mk (c : centralizer Janko4.a) :
    cubicQuotient.projection (QuotientGroup.mk' (core Janko4.a) c) =
      Janko4.InvolutionCentralizers.First.QuotientExtension.quotientConjugation
        (Janko4.InvolutionCentralizers.First.centralizerExtension.rightHom c) := by
  rw [Janko4.InvolutionCentralizers.First.centralizerExtension_rightHom]
  rfl

end ModelHypotheses

end Theory.GroupTheory.Recognition.JankoFour
