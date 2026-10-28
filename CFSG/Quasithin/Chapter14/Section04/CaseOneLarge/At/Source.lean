module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Exchanged

/-!
# The guarded large-case conclusion on the original flag

The completed large-case exclusion reduces the original extraspecial closure
to order 32, which is the input of the independent 14.4.3 branch. The guarded
application uses the actual higher-rank hypothesis and evaluates every earlier
implication at the supplied original G,T and multiple-overgroup guard.

The exact Chapter 10 MixedSizeInput and the genuine earlier source implications
remain explicit. Their discharge and the other recognition branches belong to
the final 14.4.14 assembly; this module does not assert unconditional 14.4.14.
Source: Aschbacher--Smith, 14.4.13--14, printed p.1012; refs/quasithin.pdf.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The extraspecial branch on the original flag has order 32. The large
alternative is excluded by the completed source argument; the only mixed
tensor premise is the exact independent Chapter 10 size input. -/
theorem source_extraspecial_order_eq_thirtyTwo_of_mixed_size_at
    (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) : Nat.card F.U = 32 := by
  rcases (CaseOneGeometry.source_extraspecial_order_at d earlier hq chosen
    structural alternatives F hne hZ).2 with hsmall | hlarge
  · exact hsmall
  · exact (source_large_exclusion_of_mixed_size_at d earlier hq chosen structural
      alternatives classification size F hne hZ hlarge).elim

/-- Apply the large-case exclusion to the actual guarded Theorem D branch.
Every earlier implication is evaluated at its original G,T and the supplied
multiple-overgroup guard. The chosen module and quotient marking are those
of the original higher-rank hypothesis. -/
theorem source_guarded_large_exclusion_of_mixed_size
    (d : Counterexample T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (earlier : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Earlier1332CaseOneAt T)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) : False :=
  source_large_exclusion_of_mixed_size_at d (earlier hmany) setup.quotient_model
    setup.chosen (structural hmany) (alternatives hmany) (classification hmany)
    size F hne hZ hlarge

/-- The guarded consumer reduces the original extraspecial source branch to
the order-32 input of 14.4.3. Its recognition belongs to the independent
small-branch owner; no model isomorphism is assumed in this reduction. -/
theorem source_guarded_extraspecial_order_of_mixed_size
    (d : Counterexample T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (earlier : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Earlier1332CaseOneAt T)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) : Nat.card F.U = 32 :=
  source_extraspecial_order_eq_thirtyTwo_of_mixed_size_at d (earlier hmany)
    setup.quotient_model setup.chosen (structural hmany) (alternatives hmany)
    (classification hmany) size F hne hZ

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
