module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions

/-!+# Model geometry needed by the ordinary Lie rows of 15.1.22

These contracts specify the missing model constructions, independently of
the placement argument (*). The rank-two construction supplies a second
maximal parabolic escaping the marked one. The linear construction supplies
a generating family and the flag description of every proper Sylow
overgroup under the original model equivalence.

Neither contract identifies M ∩ L, places a family member in M, or assumes
the residual centralizer identity. Those are deductions in the consumer.
The family uses the literal P N_S(L) quotient from `ParabolicPlacement`.
Source: Aschbacher--Smith, printed pp.1099--1100, ordinary cases (4),(7).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Local geometry of the two actual parabolics over S_L. Constructing
this data from each rank-two model is a separate mathematical obligation. -/
structure OrdinaryRankTwoParabolicGeometry (d : CaseIComponentData T M Mc V) where
  other : Subgroup G
  marked_parabolic : d.OrdinaryParabolic d.ML
  marked_maximal : IsCoatom (d.ML.subgroupOf d.L)
  other_parabolic : d.OrdinaryParabolic other
  other_maximal : IsCoatom (other.subgroupOf d.L)
  other_source : d.IsSourceParabolic other
  other_escape : ¬ other ≤ d.ML

/-- Local flag geometry, before applying (*) to place the generating
family. The overgroup statement concerns every proper overgroup of S_L. -/
structure OrdinaryLinearParabolicGeometry (d : CaseIComponentData T M Mc V) {n : ℕ}
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) where
  family : Set (Subgroup G)
  members : family ⊆ d.sourceParabolics
  generated : d.ML ⊔ sSup family = d.L
  flag_overgroups : ∀ K : Subgroup G, d.SL ≤ K → K < d.L →
    d.OrdinaryLinearParabolic e K

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
