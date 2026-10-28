module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Applications
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Centralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.NativeInvolutions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Classes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientClasses

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.CommonCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.TorusSplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.OuterSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.GraphConjugate
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.InnerSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.OddOuter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.EndpointFusion

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCosets

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.ShortSpace
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.ShortNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.ShortCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Original chosen-module applications of U₅(4) ambient geometry

The original Hypothesis1221 and many-maximal-overgroup assumptions construct
the whole-reduced input. The source proofs retain the selected extension,
both endpoint maps, the whole residual H and the whole-middle action.

They supply the actual parabolic core normalizers, long-root TI geometry,
full long centralizers, the two Hermitian involution classes, and full
Thompson fusion. The represented full fixed Sylow is now placed in the
ambient involution centralizer. The accepted actor representation and
numerical contradiction prove S=T unconditionally, with odd outer degree
for this same extension and class comparison on both entire endpoints.

The same original short centralizer has its actual unique fixed cosets,
F.4.42 quotient arguments and full ambient containment. The Chapter 6
same-extension F.4.43 order and literal completion provide the actual
Chapter 12 recognition and unitary-five GlobalExit.
Source: Aschbacher–Smith, printed pp.658–659,291–296,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original whole-reduced chosen-module row supplies the ambient local
hypotheses and long-root TI group without extra centralizer or fusion premises. -/
theorem rankOne_unitaryFive_ambient_local_conditions (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    pResidual 2 G = ⊤ ∧
      (∀ i : Fin 2,
        let P := ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i
        P.pCoreIn 2 = (![L,residual H] i).pCoreIn 2 ∧
        normalizer ((center (P.pCoreIn 2)).map (P.pCoreIn 2).subtype : Set G) =
          normalizer (![L,residual H] i : Set G)) ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) ∧
      Nat.card (center (residual H)) = 4 ∧
      IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
      ChapterI.Section06To08.IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
      normalizer ((center (residual H)).map (residual H).subtype : Set G) =
        normalizer (residual H : Set G) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_ambient_local_conditions hi hH hp U hc

/-- The source plane-core center, involution locus and Thompson subgroup,
using the original whole-reduced chosen-module input. -/
theorem rankOne_unitaryFive_plane_core_geometry (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    let Q := L.pCoreIn 2
    (Nat.card (center Q) = 4 ^ 4 ∧ IsElementaryAbelian 2 (center Q) ∧
      center Q = commutator Q ∧ center Q = frattini Q ∧
      ∀ x : Q, x ^ 2 = 1 ↔ x ∈ center Q) ∧
      Stellmacher.elementaryAbelianMaxJ Q = (center Q).map Q.subtype := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitaryFive_plane_core_structure hi hH hp U hc,
    d.unitaryFive_plane_core_thompson hi hH hp U hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
