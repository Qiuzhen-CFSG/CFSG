module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.UnitaryFourSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalCatalogue

/-!
# Original Chapter 12 comparisons from the reduced quadratic profile

Apply the completed U₄ source equations to the literal reduced pair and then
restore its entire original Borel. The prepared nonsolvable endpoints exclude
the binary parameter internally. The existing native extension theorem keeps
both original endpoint squares, including the possible degree-two U₄ graph
extension. Neither an original model comparison nor S = S₀ is assumed.

The earlier profile, quotient, splitness and order-four selection remain
explicit. This is one source row, not exhaustive DGS classification.
Source: DGS (1985), (15.2), pp.226--228; Aschbacher--Smith F.1.12,
pp.263--264, and the chosen-module application, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource
open FongSeitzBinary OriginalExtension SuzukiContainment

variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L R S : Subgroup G} {P : Fin 2 → Subgroup X}
  (h : HypothesisF11 ![L,R] S) (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] S) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (point : Bool) (profile : Profile ![L,R] (reducedSylow ![L,R] S) F k point)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include h e split hrot profile hk in
/-- Supply the actual reduced U₄ row, in its native orientation, to the
existing original-extension catalogue. -/
theorem reduced_alternative :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives L R S :=
  .unitaryFour m (NeZero.pos m) point
    ⟨reducedComparison h Q e split hrot point profile m hk⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.Assembly.UnitaryFourSource
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (point : Bool)
  (profile : Profile ![L,R] (reducedSylow ![L,R] (sourceS L H)) F k point)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include d h hTH hp e split hrot profile hk in
/-- The original prepared nonsolvable endpoints force a nonbinary field;
this is derived from the source comparison, not a new consumer hypothesis. -/
theorem quadratic_profile_degree : 1 < m :=
  d.unitaryFour_reduced_parameter h hTH hp m (NeZero.pos m) point
    (reducedComparison (d.hypothesisF11 h hTH) Q e split hrot point profile m hk)

include d h hTH hp e split hrot profile hk in
/-- Restoring the actual reduced quadratic profile constructs the ORIGINAL
comparison, retaining the ordinary and degree-two graph-extension branches. -/
theorem comparison_of_reduced_quadratic_profile :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) :=
  d.concreteComparison_of_reduced_alternatives h hTH hp
    (reduced_alternative (d.hypothesisF11 h hTH) Q e split hrot point profile m hk)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.Assembly.UnitaryFourSource
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4) (point : Bool)
  (profile : Profile ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) F k point)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include D h hmany hn hpsl hH d hp e split hrot profile hk in
/-- The chosen-module consumer obtains an original comparison from the
reduced source profile on the SAME arbitrary selected perfect R. -/
theorem rankOne_comparison_of_reduced_quadratic_profile :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_reduced_quadratic_profile
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp Q e split hrot
    point profile m hk

omit d hp e profile in
include D h hmany hn hpsl hH split hrot hk in
/-- Once the selected factor is the whole residual, this constructed original
comparison feeds the completed U₄ ambient recognizer and its strict GlobalExit. -/
theorem rankOne_globalExit_of_reduced_quadratic_profile
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam)
    (profile : Profile ![L,residual H]
      (reducedSylow ![L,residual H] (Global.sourceS L H)) F k point) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_of_reduced_quadratic_profile h hmany hn hpsl hH d hp
      Q e split hrot point profile m hk)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
