module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Source
public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSizeConsumers

/-!
# The original extraspecial closure has order thirty-two

The proved mixed A₅/S₃ size bound supplies the last numerical input of
14.4.13. Thus the actual nonabelian closure with center equal to the marked
point has order 32. All earlier source implications remain at the original
G,T; no mixed-size, large-action, or recognition premise is added.

Source: Aschbacher--Smith 14.4.13--14, printed p.1012, with F.1.12(I).
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual extraspecial branch of 14.4.14, with the mixed-size input
discharged by the original DGS theorem. -/
theorem source_extraspecial_order_eq_thirtyTwo_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (earlier : Earlier1332CaseOneAt T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) : Nat.card F.U = 32 :=
  source_extraspecial_order_eq_thirtyTwo_of_mixed_size_at d earlier
    h.quotient_model h.chosen structural alternatives classification
    Chapter10.MixedZeroCore.mixedSizeInput_from_dgs_source F hne hZ

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
