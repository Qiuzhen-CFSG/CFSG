module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSourceCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2NativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityAllDegrees

/-!
# Chapter 12 application of the strict linear catalogue

For an actual prepared Chapter 12 pair, the preparation supplies the strict
F.1.1 hypothesis and nonsolvability of the first parabolic. These proofs
remain named inputs to keep the geometric contracts small. The
source-selected Cartan reflections are therefore constructed internally by
the DGS assembly. The branch retains its critical pair, nontrivial
commutator, `b = 2`, the original left PSL₂ marking, chosen-apartment
exchange, and root signs for the image of the whole original Borel.

The native reduced G₂ and triality rows feed the existing restoration
theorems for the same prepared perfect right factor. The result is the full
comparison for the literal original source parabolic amalgam, including its
whole Borel and both inclusion squares. It does not strengthen the source
to a common-field hypothesis. The exchange-only application discharges the
whole-Borel signs with the source root-rigidity theorem, retaining the actual
exchange premise and the earlier explicit-sign interface.

Source: DGS (1985), (10.10), p.164; (14.1)--(14.2), pp.210--211; Theorem D,
p.224; Aschbacher--Smith F.1.12, pp.263--264,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B R : Subgroup G}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
local notation "S" => Global.sourceS L H
local notation "F" => Reduction.reducedFamily ![L,R] S
include D h hmany hn hpsl hH

/-- The strict branch's exact surviving source contract at Chapter 12. -/
theorem rankOne_strict_linear_catalogue_of_source_inputs
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (hF11 : CFSG.Quasithin.ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H))
    (hns : ¬ Group.IsSolvable (parabolic ![L,R] (Global.sourceS L H) 0))
    (hlinear : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false), Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (hexchange : StrictSourceExchange
      hF11 hc hne hb hβu hns hlinear)
    (hsign : StrictSourceRootSigns
      hF11 hc hne hb hβu hns hlinear) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] S) := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases strict_source_linear_hexagon_native_alternatives hF11 hc hne hb hβu hns hlinear
      hexchange hsign with ⟨K,hK,hfin,hchar,short,⟨e⟩⟩ | ⟨m,hm,point,⟨e⟩⟩
  · exact OriginalExtension.concreteComparison_of_reduced_g2
      d input hH.1.1.2 hp K short e
  · exact OriginalExtension.concreteComparison_of_reduced_triality_all_degrees
      d input hH.1.1.2 hp m hm point e

/-- The original Chapter 12 comparison with the whole-Borel root-sign input
discharged by source geometry. The chosen-apartment exchange remains explicit. -/
theorem rankOne_strict_linear_catalogue_of_exchange
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (hF11 : CFSG.Quasithin.ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H))
    (hns : ¬ Group.IsSolvable (parabolic ![L,R] (Global.sourceS L H) 0))
    (hlinear : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false), Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (hexchange : StrictSourceExchange hF11 hc hne hb hβu hns hlinear) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] S) := by
  exact D.rankOne_strict_linear_catalogue_of_source_inputs h hmany hn hpsl hH
    d hp hF11 hns hlinear hc hne hb hβu hexchange
    (strict_source_root_signs_of_exchange hF11 hc hne hb hβu hns hlinear hexchange)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
