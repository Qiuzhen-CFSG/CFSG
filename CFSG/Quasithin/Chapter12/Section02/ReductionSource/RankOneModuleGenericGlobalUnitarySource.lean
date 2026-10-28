module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.Commutators
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.LongCentralization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.SingularCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.QuotientCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.FullStabilizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ResidualReturn
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.MarkedCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.DegreeConflict
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.FieldTransfer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.OddField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.OddRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.NormalizerGrowth
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.GraphCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.TorusSplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.OuterFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.Five

/-!
# Original chosen-module consumers of unitary involution placement

The whole-reduced-module input constructs the rank-one generic input with the
full KnownSimple catalogue. The actual ordinary or degree-two comparison then
puts involutions of the reduced overlap, common Sylow, or either residual into
an original residual two-core. The conjugators remain in the source endpoints
or their full-normalizer join. No equality of the inner Sylow with the ambient
Sylow and no full-normalizer realization is assumed or concluded.

This is the local placement step of Aschbacher–Smith F.4.35 in the prepared
5.3 and 12.2 setup, printed pp.292,658–659,795 (`refs/quasithin.pdf`).

The public source surface also includes the completed U₄ and U₅ producers:
their constructed full-normalizer extensions satisfy the ambient order
comparison and feed the literal completion, recognition and GlobalExit
applications, without extra source premises.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Both maps of the whole reduced overlap, with the original residual cores. -/
theorem rankOne_unitary_reduced_overlap_involution_placement
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (x : G)
    (hx : x ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1)
    (hx2 : x ^ 2 = 1) :
    (∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0,
      g * x * g⁻¹ ∈ (residual H).pCoreIn 2) ∨
    (∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
      g * x * g⁻¹ ∈ L.pCoreIn 2) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_reduced_overlap_involution_placement hi hH hp m hm hc x hx hx2

/-- The reduced common Sylow retains its literal ambient embedding. -/
theorem rankOne_unitary_inner_involution_placement
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (x : G) (hx : x ∈ (T : Subgroup G) ⊓ L) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ NormalizerJoin L (residual H),
      g * x * g⁻¹ ∈ L.pCoreIn 2 ∨ g * x * g⁻¹ ∈ (residual H).pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_involution_placement hi hH hp m hm hc x hx hx2

/-- Sylow conjugacy extends the same placement to both original residuals. -/
theorem rankOne_unitary_factor_involution_placement
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (x : G) (hx : x ∈ L ∨ x ∈ residual H) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ NormalizerJoin L (residual H),
      g * x * g⁻¹ ∈ L.pCoreIn 2 ∨ g * x * g⁻¹ ∈ (residual H).pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_factor_involution_placement hi hH hp m hm hc x hx hx2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
